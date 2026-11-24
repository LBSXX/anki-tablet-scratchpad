import base64
import json
import math
import os
import socket
import threading
import time
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.parse import parse_qs, urlparse
from aqt import gui_hooks, mw
from aqt.qt import (
    QAction,
    QColor,
    QDialog,
    QPainter,
    QPainterPath,
    QPen,
    QPointF,
    Qt,
    QVBoxLayout,
    QWidget,
)
from aqt.utils import tooltip

ADDON_DIR = os.path.dirname(__file__)
PORT = 8765

state = {
    "enabled": True,
    "card_id": 0,
    "side": "question",
    "html": "En attente d'une carte sur Anki PC...",
    "counts": [0, 0, 0],
    "last_seen": 0.0,
    "pad_active": False,
    "draw_version": 0,
    "draw_data": {
        "strokes": [],
        "aspect_ratio": 1.6,
        "grid_mode": "none"
    }
}

detached_dialog = None
toggle_menu_action = None


class NativeScratchpadCanvas(QWidget):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setStyleSheet("background-color: #1e1e20;")

    def paintEvent(self, event):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.RenderHint.Antialiasing, True)
        painter.fillRect(self.rect(), QColor("#1e1e20"))

        draw = state["draw_data"]
        ratio = draw.get("aspect_ratio", 1.6)
        if not ratio or ratio < 0.2 or ratio > 5:
            ratio = 1.6

        margin = 16
        avail_w = max(100, self.width() - margin * 2)
        avail_h = max(100, self.height() - margin * 2)

        sheet_w = avail_w
        sheet_h = sheet_w / ratio
        if sheet_h > avail_h:
            sheet_h = avail_h
            sheet_w = sheet_h * ratio

        offset_x = (self.width() - sheet_w) / 2.0
        offset_y = (self.height() - sheet_h) / 2.0

        painter.setPen(Qt.PenStyle.NoPen)
        painter.setBrush(QColor("#ffffff"))
        painter.drawRoundedRect(
            int(offset_x), int(offset_y), int(sheet_w), int(sheet_h), 10, 10
        )

        grid = draw.get("grid_mode", "none")
        if grid and grid != "none":
            step = 24.0
            if grid == "grid":
                pen = QPen(QColor("#e5e9f0"), 1.0)
                painter.setPen(pen)
                x = offset_x + step
                while x < offset_x + sheet_w:
                    painter.drawLine(QPointF(x, offset_y), QPointF(x, offset_y + sheet_h))
                    x += step
                y = offset_y + step
                while y < offset_y + sheet_h:
                    painter.drawLine(QPointF(offset_x, y), QPointF(offset_x + sheet_w, y))
                    y += step
            elif grid == "dots":
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(QColor("#c5cdd8"))
                x = offset_x + step
                while x < offset_x + sheet_w:
                    y = offset_y + step
                    while y < offset_y + sheet_h:
                        painter.drawEllipse(QPointF(x, y), 1.3, 1.3)
                        y += step
                    x += step

        strokes = draw.get("strokes", [])
        ordered = [s for s in strokes if s.get("tool") == "highlighter"] + [
            s for s in strokes if s.get("tool") != "highlighter"
        ]

        for s in ordered:
            pts = s.get("points", [])
            if not pts:
                continue
            is_hl = s.get("tool") == "highlighter"
            color = QColor(s.get("color", "#1a1a1a"))
            if is_hl:
                color.setAlphaF(0.35)

            pen = QPen(color)
            pen.setWidthF(18.0 if is_hl else 2.2)
            pen.setCapStyle(Qt.PenCapStyle.FlatCap if is_hl else Qt.PenCapStyle.RoundCap)
            pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
            painter.setPen(pen)
            painter.setBrush(Qt.BrushStyle.NoBrush)

            shape = s.get("shape")
            if shape in ("line", "arrow") and len(pts) >= 2:
                x1 = offset_x + pts[0]["x"] * sheet_w
                y1 = offset_y + pts[0]["y"] * sheet_h
                x2 = offset_x + pts[-1]["x"] * sheet_w
                y2 = offset_y + pts[-1]["y"] * sheet_h
                painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))
                if shape == "arrow":
                    angle = math.atan2(y2 - y1, x2 - x1)
                    head = 13.0
                    p_left = QPointF(
                        x2 - head * math.cos(angle - math.pi / 6),
                        y2 - head * math.sin(angle - math.pi / 6),
                    )
                    p_right = QPointF(
                        x2 - head * math.cos(angle + math.pi / 6),
                        y2 - head * math.sin(angle + math.pi / 6),
                    )
                    painter.drawLine(QPointF(x2, y2), p_left)
                    painter.drawLine(QPointF(x2, y2), p_right)
                continue

            if len(pts) == 1:
                px = offset_x + pts[0]["x"] * sheet_w
                py = offset_y + pts[0]["y"] * sheet_h
                painter.setPen(Qt.PenStyle.NoPen)
                painter.setBrush(color)
                r = 9.0 if is_hl else 1.2
                painter.drawEllipse(QPointF(px, py), r, r)
                continue

            path = QPainterPath()
            path.moveTo(
                offset_x + pts[0]["x"] * sheet_w,
                offset_y + pts[0]["y"] * sheet_h,
            )
            for i in range(1, len(pts) - 1):
                xc = offset_x + ((pts[i]["x"] + pts[i + 1]["x"]) / 2.0) * sheet_w
                yc = offset_y + ((pts[i]["y"] + pts[i + 1]["y"]) / 2.0) * sheet_h
                path.quadTo(
                    offset_x + pts[i]["x"] * sheet_w,
                    offset_y + pts[i]["y"] * sheet_h,
                    xc,
                    yc,
                )
            last = pts[-1]
            path.lineTo(
                offset_x + last["x"] * sheet_w,
                offset_y + last["y"] * sheet_h,
            )
            painter.drawPath(path)


class DetachedScratchpadDialog(QDialog):
    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("Anki — Brouillon")
        self.setWindowFlags(
            Qt.WindowType.Window
            | Qt.WindowType.WindowMinimizeButtonHint
            | Qt.WindowType.WindowMaximizeButtonHint
            | Qt.WindowType.WindowCloseButtonHint
        )
        self.resize(960, 620)
        layout = QVBoxLayout(self)
        layout.setContentsMargins(0, 0, 0, 0)
        self.canvas = NativeScratchpadCanvas(self)
        layout.addWidget(self.canvas)

    def refresh(self):
        self.canvas.update()


def refresh_detached_window():
    if detached_dialog is not None and detached_dialog.isVisible():
        detached_dialog.refresh()


def open_detached_window():
    global detached_dialog
    if detached_dialog is not None:
        try:
            detached_dialog.show()
            detached_dialog.raise_()
            detached_dialog.activateWindow()
            detached_dialog.refresh()
            return
        except Exception:
            detached_dialog = None

    detached_dialog = DetachedScratchpadDialog(mw)
    detached_dialog.show()


def apply_mode_to_ui():
    enabled = state["enabled"]
    if toggle_menu_action is not None:
        toggle_menu_action.blockSignals(True)
        toggle_menu_action.setChecked(enabled)
        toggle_menu_action.blockSignals(False)

    if mw.toolbar and mw.toolbar.web:
        lbl = "Brouillon : ON" if enabled else "Brouillon : OFF"
        active_flag = "true" if enabled else "false"
        mw.toolbar.web.eval(
            f"""
            (function() {{
                const el = document.getElementById('scratchpad-top-toggle');
                if (!el) return;
                el.textContent = {json.dumps(lbl)};
                el.style.color = {active_flag} ? '#34c759' : '';
                el.style.fontWeight = '600';
            }})();
            """
        )

    if mw.reviewer and mw.reviewer.web:
        en_flag = "true" if enabled else "false"
        vis_flag = "true" if is_pad_visible_on_pc() else "false"
        draw_json = json.dumps(state["draw_data"])
        mw.reviewer.web.eval(
            f"""
            if (window.setScratchpadMode) {{
                window.setScratchpadMode({en_flag}, {vis_flag}, {draw_json});
            }}
            """
        )

    if not enabled and detached_dialog is not None and detached_dialog.isVisible():
        detached_dialog.hide()


def toggle_scratchpad_mode(*args):
    state["enabled"] = not state["enabled"]
    apply_mode_to_ui()
    tooltip("Mode brouillon activé" if state["enabled"] else "Mode brouillon désactivé")


def get_all_urls():
    ips = set()
    try:
        s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        s.connect(("8.8.8.8", 80))
        ips.add(s.getsockname()[0])
        s.close()
    except Exception:
        pass

    try:
        hostname = socket.gethostname()
        for info in socket.getaddrinfo(hostname, None, socket.AF_INET):
            ip = info[4][0]
            if not ip.startswith("127."):
                ips.add(ip)
    except Exception:
        pass

    sorted_ips = sorted(
        ips,
        key=lambda x: (
            not x.startswith("192.168.137."),
            not x.startswith("172.20.10."),
            not x.startswith("192.168."),
            x
        )
    )
    if not sorted_ips:
        return [f"http://127.0.0.1:{PORT}"]
    return [f"http://{ip}:{PORT}" for ip in sorted_ips]


def get_due_counts():
    try:
        if mw.col and mw.col.sched:
            c = mw.col.sched.counts()
            return [int(c[0]), int(c[1]), int(c[2])]
    except Exception:
        pass
    return [0, 0, 0]


def is_pad_visible_on_pc():
    return state["enabled"] and state["pad_active"] and ((time.time() - state["last_seen"]) < 3.5)


class ScratchpadHandler(BaseHTTPRequestHandler):
    def log_message(self, format, *args):
        pass

    def address_string(self):
        return self.client_address[0]

    def _send_bytes(self, content_type, data_bytes):
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(data_bytes)))
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store, no-cache, must-revalidate")
        self.send_header("Connection", "close")
        self.end_headers()
        self.wfile.write(data_bytes)

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path

        if path == "/":
            state["last_seen"] = time.time()
            with open(os.path.join(ADDON_DIR, "client.html"), "rb") as f:
                self._send_bytes("text/html; charset=utf-8", f.read())
        elif path == "/state":
            state["last_seen"] = time.time()
            if "pad=1" in self.path:
                state["pad_active"] = True
            elif "pad=0" in self.path:
                state["pad_active"] = False
            mw.taskman.run_on_main(lambda: update_pc_inline_visibility())

            payload = json.dumps({
                "card_id": state["card_id"],
                "side": state["side"],
                "html": state["html"],
                "counts": state["counts"]
            }).encode("utf-8")
            self._send_bytes("application/json; charset=utf-8", payload)
        else:
            self.send_response(404)
            self.end_headers()

    def do_POST(self):
        state["last_seen"] = time.time()
        length = int(self.headers.get("Content-Length", 0))
        body = self.rfile.read(length).decode("utf-8") if length > 0 else "{}"
        data = json.loads(body)

        if self.path == "/draw":
            state["pad_active"] = True
            draw_obj = {
                "strokes": data.get("strokes", []),
                "aspect_ratio": data.get("aspect_ratio", 1.6),
                "grid_mode": data.get("grid_mode", "none")
            }
            state["draw_data"] = draw_obj
            state["draw_version"] += 1
            mw.taskman.run_on_main(lambda d=draw_obj: on_draw_received(d))
            self._send_bytes("application/json", b'{"ok":true}')
        elif self.path == "/type":
            mw.taskman.run_on_main(lambda d=data: forward_text_to_anki(d))
            self._send_bytes("application/json", b'{"ok":true}')
        elif self.path == "/save_card":
            mw.taskman.run_on_main(lambda d=data: save_sketch_to_note(d))
            self._send_bytes("application/json", b'{"ok":true}')
        elif self.path == "/action":
            mw.taskman.run_on_main(lambda d=data: handle_review_action(d))
            self._send_bytes("application/json", b'{"ok":true}')
        else:
            self.send_response(404)
            self.end_headers()


def on_draw_received(draw_obj):
    if not state["enabled"]:
        return
    push_draw_to_inline_pc(draw_obj)
    refresh_detached_window()


def on_js_message(handled, message, context):
    if message == "ipad_open_detached":
        open_detached_window()
        return (True, None)
    elif message == "scratchpad_close_banner":
        toggle_scratchpad_mode()
        return (True, None)
    return handled


def on_top_toolbar_did_init_links(links, toolbar):
    lbl = "Brouillon : ON" if state["enabled"] else "Brouillon : OFF"
    btn = toolbar.create_link(
        cmd="scratchpad_top_btn",
        label=lbl,
        func=toggle_scratchpad_mode,
        tip="Activer ou désactiver l'affichage du brouillon sur PC",
        id="scratchpad-top-toggle",
    )
    links.append(btn)


def save_sketch_to_note(data):
    try:
        if not mw.reviewer or not mw.reviewer.card:
            return
        b64_data = data.get("image", "")
        if "," in b64_data:
            b64_data = b64_data.split(",", 1)[1]
        img_bytes = base64.b64decode(b64_data)

        card = mw.reviewer.card
        note = card.note()
        filename = f"brouillon_{note.id}_{int(time.time())}.png"
        media_dir = mw.col.media.dir()
        filepath = os.path.join(media_dir, filename)
        with open(filepath, "wb") as f:
            f.write(img_bytes)

        field_names = list(note.keys())
        target_field = field_names[-1]
        for candidate in ["Brouillon", "Scratchpad", "Extra", "Remarques"]:
            for fn in field_names:
                if fn.lower() == candidate.lower():
                    target_field = fn
                    break

        img_tag = f'<div class="ipad-scratchpad-saved"><img src="{filename}" style="max-width:100%; border:1px solid #ccc; border-radius:6px; margin-top:8px;"></div>'
        note[target_field] = (note[target_field] + "<br>" + img_tag) if note[target_field].strip() else img_tag
        mw.col.update_note(note)

        if mw.reviewer.state == "answer":
            mw.reviewer._showAnswer()
        tooltip(f"Brouillon enregistré dans « {target_field} »")
    except Exception as e:
        tooltip(f"Erreur sauvegarde : {e}")


def handle_review_action(data):
    if not mw.reviewer:
        return
    cmd = data.get("cmd")
    if cmd == "open_detached":
        open_detached_window()
    elif cmd == "show_answer":
        if mw.reviewer.card and mw.reviewer.state == "question":
            mw.reviewer._showAnswer()
    elif cmd == "answer":
        if mw.reviewer.card and mw.reviewer.state == "answer":
            ease = int(data.get("ease", 3))
            cnt = mw.col.sched.answerButtons(mw.reviewer.card)
            if ease > cnt:
                ease = cnt
            mw.reviewer._answerCard(ease)
    elif cmd == "undo_card":
        try:
            mw.onUndo()
        except Exception:
            pass
    elif cmd == "skip_card":
        if mw.reviewer.card:
            try:
                mw.col.sched.buryCards([mw.reviewer.card.id])
                mw.reviewer.nextCard()
            except Exception:
                pass
    elif cmd == "suspend_card":
        if mw.reviewer.card:
            try:
                mw.col.sched.suspendCards([mw.reviewer.card.id])
                mw.reviewer.nextCard()
                tooltip("Carte suspendue")
            except Exception:
                pass


def update_pc_inline_visibility():
    state["counts"] = get_due_counts()
    if mw.reviewer and mw.reviewer.web:
        en_flag = "true" if state["enabled"] else "false"
        vis_flag = "true" if is_pad_visible_on_pc() else "false"
        mw.reviewer.web.eval(
            f"if(window.setScratchpadMode) window.setScratchpadMode({en_flag}, {vis_flag}, null);"
        )


def push_draw_to_inline_pc(draw_obj):
    if not state["enabled"]:
        return
    if mw.reviewer and mw.reviewer.web:
        js = f"if(window.receiveInlineDraw) window.receiveInlineDraw({json.dumps(draw_obj)});"
        mw.reviewer.web.eval(js)


def forward_text_to_anki(data):
    if mw.reviewer and mw.reviewer.web:
        js = f"if(window.receiveTypedText) window.receiveTypedText({json.dumps(data)});"
        mw.reviewer.web.eval(js)


def inject_pad_script(clear_canvas=False):
    urls_text = "  ou  ".join(get_all_urls())
    clear_flag = "true" if clear_canvas else "false"
    enabled_flag = "true" if state["enabled"] else "false"
    initial_vis = "true" if is_pad_visible_on_pc() else "false"
    initial_draw_json = json.dumps(state["draw_data"])
    inject_js = f"""
    setTimeout(function() {{
        const qa = document.getElementById('qa') || document.body;

        let banner = document.getElementById('pc-mirror-banner');
        if (!banner) {{
            banner = document.createElement('div');
            banner.id = 'pc-mirror-banner';
            banner.style.cssText = 'max-width: 860px; margin: 12px auto 6px auto; padding: 6px 12px; border-radius: 7px; font-family: sans-serif; font-size: 12.5px; display: none; justify-content: space-between; align-items: center; background: #eef4ff; color: #1a3b70; border: 1px solid #b8d0ff; user-select: text;';
            qa.appendChild(banner);
        }}
        banner.innerHTML = '<span>Lien brouillon : <strong>{urls_text}</strong></span>' +
            '<div style="display:flex; gap:6px;">' +
            '<button id="btn-detach-pad" style="padding: 4px 10px; border: none; border-radius: 5px; background: #007aff; color: #fff; font-weight: 600; cursor: pointer; font-size: 12px;">⧉ Détacher</button>' +
            '<button id="btn-hide-pad" title="Masquer le mode brouillon" style="padding: 4px 8px; border: none; border-radius: 5px; background: #d1d5db; color: #1f2937; font-weight: 700; cursor: pointer; font-size: 12px;">✕</button>' +
            '</div>';

        document.getElementById('btn-detach-pad').onclick = function() {{
            if (typeof pycmd === 'function') {{
                pycmd('ipad_open_detached');
            }}
        }};
        document.getElementById('btn-hide-pad').onclick = function() {{
            if (typeof pycmd === 'function') {{
                pycmd('scratchpad_close_banner');
            }}
        }};

        let textMirror = document.getElementById('pc-mirror-text');
        if (!textMirror) {{
            textMirror = document.createElement('div');
            textMirror.id = 'pc-mirror-text';
            textMirror.style.cssText = 'display: none; max-width: 860px; margin: 6px auto; padding: 10px 14px; border-radius: 8px; font-family: sans-serif; font-size: 16px; background: #f8f9fa; color: #111; border: 1px solid #dadce0; white-space: pre-wrap;';
            qa.appendChild(textMirror);
        }}

        let padWrap = document.getElementById('pc-mirror-wrap');
        if (!padWrap) {{
            padWrap = document.createElement('div');
            padWrap.id = 'pc-mirror-wrap';
            padWrap.style.cssText = 'display: none; position: relative; margin: 8px auto 16px auto; border: 2px solid #007aff; background: #ffffff; border-radius: 10px; box-shadow: 0 3px 12px rgba(0,0,0,0.08); user-select: none; box-sizing: border-box;';

            const pad = document.createElement('canvas');
            pad.id = 'pc-mirror-pad';
            pad.style.cssText = 'display: block; width: 100%; height: 100%; border-radius: 8px;';
            padWrap.appendChild(pad);

            const edges = [
                {{ dir: 'e',  css: 'position:absolute; top:6px; right:-5px; width:10px; bottom:14px; cursor:ew-resize;' }},
                {{ dir: 'w',  css: 'position:absolute; top:6px; left:-5px; width:10px; bottom:14px; cursor:ew-resize;' }},
                {{ dir: 's',  css: 'position:absolute; left:6px; right:14px; bottom:-5px; height:10px; cursor:ns-resize;' }},
                {{ dir: 'se', css: 'position:absolute; right:2px; bottom:2px; width:16px; height:16px; cursor:nwse-resize; background:linear-gradient(135deg, transparent 50%, #007aff 50%); border-bottom-right-radius:6px; opacity:0.85;' }}
            ];
            edges.forEach(function(h) {{
                const el = document.createElement('div');
                el.style.cssText = h.css + ' z-index: 10;';
                el.title = 'Tirer pour redimensionner';
                el.addEventListener('mousedown', function(e) {{
                    e.preventDefault();
                    e.stopPropagation();
                    const startX = e.clientX;
                    const startY = e.clientY;
                    const rect = padWrap.getBoundingClientRect();
                    const startW = rect.width;
                    const startH = rect.height;

                    function onMove(ev) {{
                        const dx = ev.clientX - startX;
                        const dy = ev.clientY - startY;
                        let newW = startW;
                        let newH = startH;
                        if (h.dir.includes('e')) newW = startW + dx * 2;
                        if (h.dir.includes('w')) newW = startW - dx * 2;
                        if (h.dir.includes('s')) newH = startH + dy;

                        newW = Math.max(260, Math.min(window.innerWidth - 24, newW));
                        newH = Math.max(150, Math.min(window.innerHeight - 60, newH));
                        window._customPadSize = {{ w: newW, h: newH }};
                        if (window._lastInlineDraw) {{
                            window.receiveInlineDraw(window._lastInlineDraw);
                        }}
                    }}

                    function onUp() {{
                        document.removeEventListener('mousemove', onMove);
                        document.removeEventListener('mouseup', onUp);
                    }}
                    document.addEventListener('mousemove', onMove);
                    document.addEventListener('mouseup', onUp);
                }});
                padWrap.appendChild(el);
            }});

            qa.appendChild(padWrap);
        }}

        const pad = document.getElementById('pc-mirror-pad');
        window._lastInlineDraw = {initial_draw_json};

        pad.ondblclick = function(e) {{
            e.preventDefault();
            e.stopPropagation();
            if (window._customPadSize) {{
                window._customPadSize = null;
            }} else {{
                window._customPadSize = {{ w: window.innerWidth - 40, h: window.innerHeight - 120 }};
            }}
            if (window._lastInlineDraw) {{
                window.receiveInlineDraw(window._lastInlineDraw);
            }}
        }};

        const ctx = pad.getContext('2d');
        if ({clear_flag}) {{
            window._savedTyped = "";
            textMirror.style.display = 'none';
            textMirror.textContent = '';
        }} else if (window._savedTyped) {{
            textMirror.style.display = 'block';
            textMirror.textContent = 'Réponse saisie : ' + window._savedTyped;
        }}

        window.setPadVisibility = function(show) {{
            padWrap.style.display = show ? 'block' : 'none';
            if (show) {{
                banner.style.background = '#e6f4ea';
                banner.style.borderColor = '#34a853';
                banner.style.color = '#137333';
            }} else {{
                banner.style.background = '#eef4ff';
                banner.style.borderColor = '#b8d0ff';
                banner.style.color = '#1a3b70';
            }}
        }};

        window.setScratchpadMode = function(enabled, padShow, drawObj) {{
            if (!enabled) {{
                banner.style.display = 'none';
                padWrap.style.display = 'none';
                return;
            }}
            banner.style.display = 'flex';
            window.setPadVisibility(padShow);
            if (drawObj && padShow) {{
                window.receiveInlineDraw(drawObj);
            }}
        }};

        window.receiveTypedText = function(data) {{
            const txt = data.text || '';
            window._savedTyped = txt;
            const typeInput = document.getElementById('typeans');
            if (typeInput) {{
                typeInput.value = txt;
                typeInput.dispatchEvent(new Event('input', {{ bubbles: true }}));
                textMirror.style.display = 'none';
            }} else if (txt.trim().length > 0) {{
                textMirror.style.display = 'block';
                textMirror.textContent = 'Réponse saisie : ' + txt;
            }} else {{
                textMirror.style.display = 'none';
            }}
            if (data.submit && typeof pycmd === 'function') {{
                pycmd('ans');
            }}
        }};

        window.receiveInlineDraw = function(draw) {{
            window._lastInlineDraw = draw;
            if (banner.style.display === 'none') return;
            window.setPadVisibility(true);
            const ratio = (draw.aspect_ratio && draw.aspect_ratio > 0.2 && draw.aspect_ratio < 5) ? draw.aspect_ratio : 1.6;

            let cssW, cssH;
            if (window._customPadSize) {{
                cssW = window._customPadSize.w;
                cssH = window._customPadSize.h;
            }} else {{
                const maxW = Math.min(860, window.innerWidth - 40);
                const maxH = 440;
                cssW = maxW;
                cssH = cssW / ratio;
                if (cssH > maxH) {{
                    cssH = maxH;
                    cssW = cssH * ratio;
                }}
            }}

            padWrap.style.width = Math.round(cssW) + 'px';
            padWrap.style.height = Math.round(cssH) + 'px';

            const dpr = window.devicePixelRatio || 1;
            pad.width = Math.round(cssW * dpr);
            pad.height = Math.round(cssH * dpr);

            ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
            ctx.fillStyle = '#ffffff';
            ctx.fillRect(0, 0, cssW, cssH);

            const grid = draw.grid_mode;
            if (grid && grid !== 'none') {{
                ctx.save();
                const step = 22;
                if (grid === 'grid') {{
                    ctx.strokeStyle = '#e5e9f0';
                    ctx.lineWidth = 1;
                    ctx.beginPath();
                    for (let x = step; x < cssW; x += step) {{ ctx.moveTo(x, 0); ctx.lineTo(x, cssH); }}
                    for (let y = step; y < cssH; y += step) {{ ctx.moveTo(0, y); ctx.lineTo(cssW, y); }}
                    ctx.stroke();
                }} else if (grid === 'dots') {{
                    ctx.fillStyle = '#c5cdd8';
                    for (let x = step; x < cssW; x += step) {{
                        for (let y = step; y < cssH; y += step) {{ ctx.fillRect(x - 1, y - 1, 2, 2); }}
                    }}
                }}
                ctx.restore();
            }}

            const all = draw.strokes || [];
            const drawGroup = (list) => {{
                for (const s of list) {{
                    const pts = s.points;
                    if (!pts || pts.length === 0) continue;
                    const isHl = s.tool === 'highlighter';
                    ctx.save();
                    ctx.lineCap = isHl ? 'butt' : 'round';
                    ctx.lineJoin = 'round';
                    ctx.globalAlpha = isHl ? 0.35 : 1.0;
                    ctx.strokeStyle = s.color || '#1a1a1a';
                    ctx.fillStyle = s.color || '#1a1a1a';
                    ctx.lineWidth = isHl ? 15 : 2.0;

                    ctx.beginPath();
                    if (s.shape === 'line' || s.shape === 'arrow') {{
                        const x1 = pts[0].x * cssW, y1 = pts[0].y * cssH;
                        const x2 = pts[pts.length - 1].x * cssW, y2 = pts[pts.length - 1].y * cssH;
                        ctx.moveTo(x1, y1);
                        ctx.lineTo(x2, y2);
                        if (s.shape === 'arrow') {{
                            const angle = Math.atan2(y2 - y1, x2 - x1);
                            const head = 11;
                            ctx.moveTo(x2, y2);
                            ctx.lineTo(x2 - head * Math.cos(angle - Math.PI / 6), y2 - head * Math.sin(angle - Math.PI / 6));
                            ctx.moveTo(x2, y2);
                            ctx.lineTo(x2 - head * Math.cos(angle + Math.PI / 6), y2 - head * Math.sin(angle + Math.PI / 6));
                        }}
                        ctx.stroke();
                        ctx.restore();
                        continue;
                    }}
                    if (pts.length === 1) {{
                        ctx.arc(pts[0].x * cssW, pts[0].y * cssH, isHl ? 7.5 : 1.1, 0, Math.PI * 2);
                        ctx.fill();
                        ctx.restore();
                        continue;
                    }}
                    ctx.moveTo(pts[0].x * cssW, pts[0].y * cssH);
                    for (let i = 1; i < pts.length - 1; i++) {{
                        const xc = ((pts[i].x + pts[i + 1].x) / 2) * cssW;
                        const yc = ((pts[i].y + pts[i + 1].y) / 2) * cssH;
                        ctx.quadraticCurveTo(pts[i].x * cssW, pts[i].y * cssH, xc, yc);
                    }}
                    const last = pts[pts.length - 1];
                    ctx.lineTo(last.x * cssW, last.y * cssH);
                    ctx.stroke();
                    ctx.restore();
                }}
            }};
            drawGroup(all.filter(s => s.tool === 'highlighter'));
            drawGroup(all.filter(s => s.tool !== 'highlighter'));
        }};

        window.setScratchpadMode({enabled_flag}, {initial_vis}, {initial_draw_json});
    }}, 60);
    """
    mw.reviewer.web.eval(inject_js)


def on_show_question(card):
    state["card_id"] += 1
    state["side"] = "question"
    state["html"] = card.question()
    state["counts"] = get_due_counts()
    state["draw_data"] = {
        "strokes": [],
        "aspect_ratio": state["draw_data"].get("aspect_ratio", 1.6),
        "grid_mode": state["draw_data"].get("grid_mode", "none")
    }
    state["draw_version"] += 1
    inject_pad_script(clear_canvas=True)
    refresh_detached_window()


def on_show_answer(card):
    state["side"] = "answer"
    state["html"] = card.answer()
    state["counts"] = get_due_counts()
    inject_pad_script(clear_canvas=False)


def setup_menu():
    global toggle_menu_action
    toggle_menu_action = QAction("Activer le mode brouillon sur PC", mw)
    toggle_menu_action.setCheckable(True)
    toggle_menu_action.setChecked(state["enabled"])
    toggle_menu_action.triggered.connect(toggle_scratchpad_mode)
    mw.form.menuTools.addAction(toggle_menu_action)

    open_action = QAction("Ouvrir le brouillon en fenêtre flottante", mw)
    open_action.triggered.connect(open_detached_window)
    mw.form.menuTools.addAction(open_action)
    apply_mode_to_ui()


def start_server():
    try:
        server = ThreadingHTTPServer(("0.0.0.0", PORT), ScratchpadHandler)
        server.serve_forever()
    except Exception:
        pass


threading.Thread(target=start_server, daemon=True).start()
gui_hooks.reviewer_did_show_question.append(on_show_question)
gui_hooks.reviewer_did_show_answer.append(on_show_answer)
gui_hooks.main_window_did_init.append(setup_menu)
gui_hooks.webview_did_receive_js_message.append(on_js_message)
gui_hooks.top_toolbar_did_init_links.append(on_top_toolbar_did_init_links)
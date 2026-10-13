"""Vetorial - editor de desenho vetorial simples feito com Tkinter.

Ferramentas: selecionar/mover, retângulo, elipse, linha, lápis e texto.
Recursos: cores de contorno e preenchimento, espessura, desfazer/refazer,
duplicar, ordem das camadas, salvar/abrir (.vetorial) e exportar SVG.
"""
import copy
import json
import math
import tkinter as tk
from tkinter import colorchooser, filedialog, messagebox, simpledialog, ttk
from xml.sax.saxutils import escape

APP_NAME = "Vetorial"
FILE_EXT = ".vetorial"
TOOLS = [
    ("select", "Selecionar", "v"),
    ("rect", "Retângulo", "r"),
    ("oval", "Elipse", "e"),
    ("line", "Linha", "l"),
    ("pen", "Lápis", "p"),
    ("text", "Texto", "t"),
]
TOOL_NAMES = {key: name for key, name, _ in TOOLS}
FILLABLE = ("rect", "oval")
HIT = 4  # tolerância (px) ao clicar em uma forma
MAX_UNDO = 200


class VectorApp:
    def __init__(self, root):
        self.root = root
        self.shapes = []
        self.undo_stack = []
        self.redo_stack = []
        self.selected = None
        self.item_map = {}
        self.action = None
        self.before = None
        self.path = None
        self.dirty = False
        self.mouse = (0, 0)

        self.tool = tk.StringVar(value="rect")
        self.stroke = "#1f2937"
        self.fill = "#93c5fd"
        self.width = tk.IntVar(value=3)

        self._build_menu()
        self._build_toolbar()
        self._build_canvas()
        self._bind_keys()
        self.tool.trace_add("write", lambda *_: self._on_tool_change())
        self.root.protocol("WM_DELETE_WINDOW", self.quit)
        self._update_title()
        self._status()

    # ------------------------------------------------------------ interface
    def _build_menu(self):
        menu = tk.Menu(self.root)
        f = tk.Menu(menu, tearoff=0)
        f.add_command(label="Novo", accelerator="Ctrl+N", command=self.new)
        f.add_command(label="Abrir...", accelerator="Ctrl+O", command=self.open)
        f.add_command(label="Salvar", accelerator="Ctrl+S", command=self.save)
        f.add_command(label="Salvar como...", accelerator="Ctrl+Shift+S", command=self.save_as)
        f.add_separator()
        f.add_command(label="Exportar SVG...", accelerator="Ctrl+E", command=self.export_svg)
        f.add_separator()
        f.add_command(label="Sair", command=self.quit)
        menu.add_cascade(label="Arquivo", menu=f)

        e = tk.Menu(menu, tearoff=0)
        e.add_command(label="Desfazer", accelerator="Ctrl+Z", command=self.undo)
        e.add_command(label="Refazer", accelerator="Ctrl+Y", command=self.redo)
        e.add_separator()
        e.add_command(label="Duplicar", accelerator="Ctrl+D", command=self.duplicate)
        e.add_command(label="Excluir", accelerator="Del", command=self.delete_selected)
        e.add_separator()
        e.add_command(label="Trazer para frente", accelerator="Ctrl+]", command=self.bring_front)
        e.add_command(label="Enviar para trás", accelerator="Ctrl+[", command=self.send_back)
        menu.add_cascade(label="Editar", menu=e)

        h = tk.Menu(menu, tearoff=0)
        h.add_command(label="Atalhos", command=self.show_help)
        menu.add_cascade(label="Ajuda", menu=h)
        self.root.config(menu=menu)

    def _build_toolbar(self):
        bar = ttk.Frame(self.root, padding=(6, 4))
        bar.pack(side="top", fill="x")
        for key, name, shortcut in TOOLS:
            ttk.Radiobutton(
                bar, text=f"{name} ({shortcut.upper()})", value=key,
                variable=self.tool, style="Toolbutton",
            ).pack(side="left", padx=1)

        ttk.Separator(bar, orient="vertical").pack(side="left", fill="y", padx=8)
        ttk.Label(bar, text="Contorno").pack(side="left")
        self.stroke_swatch = self._swatch(bar, self.pick_stroke)
        ttk.Label(bar, text="Preenchimento").pack(side="left", padx=(8, 0))
        self.fill_swatch = self._swatch(bar, self.pick_fill)
        ttk.Button(bar, text="Sem preench.", command=self.clear_fill).pack(side="left", padx=2)

        ttk.Label(bar, text="Espessura").pack(side="left", padx=(10, 2))
        spin = ttk.Spinbox(bar, from_=1, to=40, width=4, textvariable=self.width,
                           command=self.apply_width)
        spin.pack(side="left")
        spin.bind("<Return>", lambda e: self.apply_width())
        spin.bind("<FocusOut>", lambda e: self.apply_width())
        self._refresh_swatches()

    def _swatch(self, parent, command):
        lbl = tk.Label(parent, width=3, relief="solid", bd=1, cursor="hand2")
        lbl.pack(side="left", padx=4)
        lbl.bind("<Button-1>", lambda e: command())
        return lbl

    def _refresh_swatches(self):
        self.stroke_swatch.config(bg=self.stroke, text="")
        if self.fill:
            self.fill_swatch.config(bg=self.fill, text="")
        else:
            self.fill_swatch.config(bg="white", text="✕", fg="#dc2626")

    def _build_canvas(self):
        self.status_bar = ttk.Label(self.root, anchor="w", padding=(8, 2))
        self.status_bar.pack(side="bottom", fill="x")
        self.canvas = tk.Canvas(self.root, bg="white", highlightthickness=0, cursor="crosshair")
        self.canvas.pack(fill="both", expand=True)
        c = self.canvas
        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Double-Button-1>", self.on_double)
        c.bind("<Motion>", self.on_motion)

    def _bind_keys(self):
        r = self.root
        r.bind("<Control-n>", lambda e: self.new())
        r.bind("<Control-o>", lambda e: self.open())
        r.bind("<Control-s>", lambda e: self.save())
        r.bind("<Control-S>", lambda e: self.save_as())
        r.bind("<Control-e>", lambda e: self.export_svg())
        r.bind("<Control-z>", lambda e: self.undo())
        r.bind("<Control-y>", lambda e: self.redo())
        r.bind("<Control-d>", lambda e: self.duplicate())
        r.bind("<Control-bracketright>", lambda e: self.bring_front())
        r.bind("<Control-bracketleft>", lambda e: self.send_back())

        c = self.canvas
        c.bind("<Delete>", lambda e: self.delete_selected())
        c.bind("<BackSpace>", lambda e: self.delete_selected())
        c.bind("<Escape>", lambda e: self.select(None))
        for key, _, shortcut in TOOLS:
            c.bind(f"<KeyPress-{shortcut}>", lambda e, k=key: self.tool.set(k))
        arrows = {"Left": (-1, 0), "Right": (1, 0), "Up": (0, -1), "Down": (0, 1)}
        for keysym, (dx, dy) in arrows.items():
            c.bind(f"<{keysym}>", lambda e, d=(dx, dy): self.nudge(*d))
            c.bind(f"<Shift-{keysym}>", lambda e, d=(dx * 10, dy * 10): self.nudge(*d))

    # --------------------------------------------------------------- estado
    def _snapshot(self):
        return copy.deepcopy(self.shapes)

    def _commit(self, before):
        self.undo_stack.append(before)
        if len(self.undo_stack) > MAX_UNDO:
            self.undo_stack.pop(0)
        self.redo_stack.clear()
        self._mark_dirty()

    def _mark_dirty(self, value=True):
        self.dirty = value
        self._update_title()
        self._status()

    def _update_title(self):
        name = self.path.replace("\\", "/").split("/")[-1] if self.path else "Sem título"
        self.root.title(f"{'*' if self.dirty else ''}{name} - {APP_NAME}")

    def _status(self):
        tool = TOOL_NAMES[self.tool.get()]
        sel = ""
        if self.selected is not None:
            sel = f"   |   Selecionado: {TOOL_NAMES[self.shapes[self.selected]['type']]}"
        x, y = self.mouse
        self.status_bar.config(
            text=f"Ferramenta: {tool}   |   Formas: {len(self.shapes)}{sel}   |   x: {x:.0f}  y: {y:.0f}"
        )

    def _on_tool_change(self):
        tool = self.tool.get()
        cursor = {"select": "arrow", "text": "xterm"}.get(tool, "crosshair")
        self.canvas.config(cursor=cursor)
        if tool != "select" and self.selected is not None:
            self.selected = None
            self.redraw()
        self._status()

    def undo(self):
        if not self.undo_stack:
            return
        self.redo_stack.append(self._snapshot())
        self.shapes = self.undo_stack.pop()
        self.selected = None
        self._mark_dirty()
        self.redraw()

    def redo(self):
        if not self.redo_stack:
            return
        self.undo_stack.append(self._snapshot())
        self.shapes = self.redo_stack.pop()
        self.selected = None
        self._mark_dirty()
        self.redraw()

    # -------------------------------------------------------------- desenho
    def redraw(self):
        c = self.canvas
        c.delete("all")
        self.item_map = {}
        sel_item = None
        for i, s in enumerate(self.shapes):
            item = self._draw_shape(s)
            if item:
                self.item_map[item] = i
                if i == self.selected:
                    sel_item = item
        if sel_item is not None:
            bb = c.bbox(sel_item)
            if bb:
                c.create_rectangle(bb[0] - 3, bb[1] - 3, bb[2] + 3, bb[3] + 3,
                                   outline="#2563eb", dash=(4, 2), width=1)
        self._status()

    def _draw_shape(self, s):
        c = self.canvas
        t, co, w = s["type"], s["coords"], s["width"]
        if t == "rect":
            return c.create_rectangle(*co, outline=s["stroke"], fill=s["fill"], width=w)
        if t == "oval":
            return c.create_oval(*co, outline=s["stroke"], fill=s["fill"], width=w)
        if t == "line":
            return c.create_line(*co, fill=s["stroke"], width=w, capstyle="round")
        if t == "pen":
            if len(co) < 4:
                return None
            return c.create_line(*co, fill=s["stroke"], width=w, capstyle="round",
                                 joinstyle="round", smooth=True)
        if t == "text":
            return c.create_text(co[0], co[1], text=s["text"], fill=s["stroke"], anchor="nw",
                                 font=("Segoe UI", -s["size"]))
        return None

    def _text_size(self, width=None):
        return 12 + 2 * (width if width is not None else self._width())

    def _width(self):
        try:
            return max(1, min(40, int(self.width.get())))
        except (tk.TclError, ValueError):
            return 3

    # ---------------------------------------------------------------- mouse
    def _pos(self, e):
        return self.canvas.canvasx(e.x), self.canvas.canvasy(e.y)

    def on_motion(self, e):
        self.mouse = self._pos(e)
        self._status()

    def on_press(self, e):
        self.canvas.focus_set()
        x, y = self._pos(e)
        tool = self.tool.get()
        self.before = self._snapshot()

        if tool == "select":
            idx = self._hit(x, y)
            self.select(idx)
            self.action = ("move", x, y, False) if idx is not None else None
            return

        if tool == "text":
            self.action = None
            txt = simpledialog.askstring("Texto", "Digite o texto:", parent=self.root)
            if txt:
                self.shapes.append({
                    "type": "text", "coords": [x, y], "text": txt, "stroke": self.stroke,
                    "fill": "", "width": self._width(), "size": self._text_size(),
                })
                self._commit(self.before)
                self.redraw()
            return

        shape = {
            "type": tool,
            "coords": [x, y] if tool == "pen" else [x, y, x, y],
            "stroke": self.stroke,
            "fill": self.fill if tool in FILLABLE else "",
            "width": self._width(),
        }
        self.shapes.append(shape)
        self.selected = None
        self.action = ("draw", len(self.shapes) - 1)
        self.redraw()

    def on_drag(self, e):
        if not self.action:
            return
        x, y = self._pos(e)
        self.mouse = (x, y)
        if self.action[0] == "draw":
            s = self.shapes[self.action[1]]
            if s["type"] == "pen":
                lx, ly = s["coords"][-2:]
                if math.hypot(x - lx, y - ly) >= 2:
                    s["coords"] += [x, y]
            else:
                x0, y0 = s["coords"][:2]
                if e.state & 0x0001:  # Shift pressionado
                    x, y = self._constrain(s["type"], x0, y0, x, y)
                s["coords"][2:] = [x, y]
            self.redraw()
        elif self.action[0] == "move" and self.selected is not None:
            _, lx, ly, _ = self.action
            self._move(self.shapes[self.selected], x - lx, y - ly)
            self.action = ("move", x, y, True)
            self.redraw()

    def on_release(self, e):
        action, self.action = self.action, None
        if not action:
            return
        if action[0] == "draw":
            idx = action[1]
            s = self.shapes[idx]
            if self._degenerate(s):
                self.shapes.pop(idx)
                self.redraw()
                return
            if s["type"] in FILLABLE:
                x0, y0, x1, y1 = s["coords"]
                s["coords"] = [min(x0, x1), min(y0, y1), max(x0, x1), max(y0, y1)]
            self._commit(self.before)
            self.redraw()
        elif action[0] == "move" and action[3]:
            self._commit(self.before)

    def on_double(self, e):
        # O 2º clique rápido chega só aqui; trata como clique normal
        # para que selecionar/arrastar/desenhar continue funcionando.
        self.on_press(e)
        if self.tool.get() != "select":
            return
        x, y = self._pos(e)
        idx = self._hit(x, y)
        if idx is None or self.shapes[idx]["type"] != "text":
            return
        self.action = None
        s = self.shapes[idx]
        txt = simpledialog.askstring("Editar texto", "Texto:", initialvalue=s["text"],
                                     parent=self.root)
        if txt and txt != s["text"]:
            before = self._snapshot()
            s["text"] = txt
            self._commit(before)
            self.redraw()

    @staticmethod
    def _constrain(kind, x0, y0, x, y):
        dx, dy = x - x0, y - y0
        if kind in FILLABLE:  # quadrado / círculo
            d = max(abs(dx), abs(dy))
            return x0 + math.copysign(d, dx or 1), y0 + math.copysign(d, dy or 1)
        # linha: ângulos de 45 em 45 graus
        ang = round(math.atan2(dy, dx) / (math.pi / 4)) * (math.pi / 4)
        length = math.hypot(dx, dy)
        return x0 + length * math.cos(ang), y0 + length * math.sin(ang)

    @staticmethod
    def _degenerate(s):
        co = s["coords"]
        if s["type"] == "pen":
            return len(co) < 4
        return abs(co[2] - co[0]) < 3 and abs(co[3] - co[1]) < 3

    @staticmethod
    def _move(s, dx, dy):
        s["coords"] = [v + (dx if i % 2 == 0 else dy) for i, v in enumerate(s["coords"])]

    def _hit(self, x, y):
        items = self.canvas.find_overlapping(x - HIT, y - HIT, x + HIT, y + HIT)
        for item in reversed(items):  # do topo para baixo
            if item in self.item_map:
                return self.item_map[item]
        return None

    # ------------------------------------------------------------- seleção
    def select(self, idx):
        self.selected = idx
        if idx is not None:
            s = self.shapes[idx]
            self.stroke = s["stroke"]
            if s["type"] in FILLABLE:
                self.fill = s["fill"]
            self.width.set(s["width"])
            self._refresh_swatches()
        self.redraw()

    def _apply_to_selected(self, **props):
        if self.selected is None:
            return
        s = self.shapes[self.selected]
        if "fill" in props and s["type"] not in FILLABLE:
            props.pop("fill")
        if "width" in props and s["type"] == "text":
            props["size"] = self._text_size(props["width"])
        if not props or all(s.get(k) == v for k, v in props.items()):
            return
        before = self._snapshot()
        s.update(props)
        self._commit(before)
        self.redraw()

    def pick_stroke(self):
        color = colorchooser.askcolor(self.stroke, title="Cor do contorno", parent=self.root)[1]
        if color:
            self.stroke = color
            self._refresh_swatches()
            self._apply_to_selected(stroke=color)

    def pick_fill(self):
        color = colorchooser.askcolor(self.fill or "#ffffff", title="Cor do preenchimento",
                                      parent=self.root)[1]
        if color:
            self.fill = color
            self._refresh_swatches()
            self._apply_to_selected(fill=color)

    def clear_fill(self):
        self.fill = ""
        self._refresh_swatches()
        self._apply_to_selected(fill="")

    def apply_width(self):
        w = self._width()
        self.width.set(w)
        self._apply_to_selected(width=w)

    def nudge(self, dx, dy):
        if self.selected is None:
            return
        before = self._snapshot()
        self._move(self.shapes[self.selected], dx, dy)
        self._commit(before)
        self.redraw()

    def duplicate(self):
        if self.selected is None:
            return
        before = self._snapshot()
        clone = copy.deepcopy(self.shapes[self.selected])
        self._move(clone, 15, 15)
        self.shapes.append(clone)
        self._commit(before)
        self.select(len(self.shapes) - 1)

    def delete_selected(self):
        if self.selected is None:
            return
        before = self._snapshot()
        self.shapes.pop(self.selected)
        self.selected = None
        self._commit(before)
        self.redraw()

    def bring_front(self):
        if self.selected is None:
            return
        before = self._snapshot()
        self.shapes.append(self.shapes.pop(self.selected))
        self.selected = len(self.shapes) - 1
        self._commit(before)
        self.redraw()

    def send_back(self):
        if self.selected is None:
            return
        before = self._snapshot()
        self.shapes.insert(0, self.shapes.pop(self.selected))
        self.selected = 0
        self._commit(before)
        self.redraw()

    # ------------------------------------------------------------ arquivos
    def _confirm_discard(self):
        if not self.dirty:
            return True
        answer = messagebox.askyesnocancel(
            APP_NAME, "Há alterações não salvas. Deseja salvar antes?", parent=self.root)
        if answer is None:
            return False
        if answer:
            return self.save()
        return True

    def new(self):
        if not self._confirm_discard():
            return
        self._load([], None)

    def _load(self, shapes, path):
        self.shapes = shapes
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.selected = None
        self.path = path
        self._mark_dirty(False)
        self.redraw()

    def open(self):
        if not self._confirm_discard():
            return
        path = filedialog.askopenfilename(
            parent=self.root, title="Abrir desenho",
            filetypes=[("Desenho Vetorial", f"*{FILE_EXT}"), ("Todos os arquivos", "*.*")])
        if not path:
            return
        try:
            with open(path, encoding="utf-8") as fh:
                data = json.load(fh)
            shapes = data["shapes"]
            if not isinstance(shapes, list):
                raise ValueError("formato inválido")
            for s in shapes:
                if s.get("type") not in TOOL_NAMES or not isinstance(s.get("coords"), list):
                    raise ValueError("forma inválida no arquivo")
        except Exception as exc:  # noqa: BLE001
            messagebox.showerror(APP_NAME, f"Não foi possível abrir o arquivo:\n{exc}",
                                 parent=self.root)
            return
        self._load(shapes, path)

    def save(self):
        if not self.path:
            return self.save_as()
        return self._write(self.path)

    def save_as(self):
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Salvar desenho", defaultextension=FILE_EXT,
            filetypes=[("Desenho Vetorial", f"*{FILE_EXT}")])
        if not path:
            return False
        return self._write(path)

    def _write(self, path):
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump({"app": APP_NAME, "version": 1, "shapes": self.shapes}, fh,
                          ensure_ascii=False, indent=1)
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Não foi possível salvar:\n{exc}", parent=self.root)
            return False
        self.path = path
        self._mark_dirty(False)
        return True

    def export_svg(self):
        path = filedialog.asksaveasfilename(
            parent=self.root, title="Exportar SVG", defaultextension=".svg",
            filetypes=[("Imagem SVG", "*.svg")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(self.to_svg())
        except OSError as exc:
            messagebox.showerror(APP_NAME, f"Não foi possível exportar:\n{exc}", parent=self.root)
            return
        messagebox.showinfo(APP_NAME, "SVG exportado com sucesso.", parent=self.root)

    def to_svg(self):
        w = max(self.canvas.winfo_width(), 1)
        h = max(self.canvas.winfo_height(), 1)
        out = [
            '<?xml version="1.0" encoding="UTF-8"?>',
            f'<svg xmlns="http://www.w3.org/2000/svg" width="{w}" height="{h}" '
            f'viewBox="0 0 {w} {h}">',
            '  <rect width="100%" height="100%" fill="white"/>',
        ]
        for s in self.shapes:
            t, co, sw = s["type"], s["coords"], s["width"]
            stroke = s["stroke"]
            fill = s["fill"] or "none"
            if t == "rect":
                x0, y0, x1, y1 = co
                out.append(f'  <rect x="{x0:.1f}" y="{y0:.1f}" width="{x1 - x0:.1f}" '
                           f'height="{y1 - y0:.1f}" fill="{fill}" stroke="{stroke}" '
                           f'stroke-width="{sw}"/>')
            elif t == "oval":
                x0, y0, x1, y1 = co
                out.append(f'  <ellipse cx="{(x0 + x1) / 2:.1f}" cy="{(y0 + y1) / 2:.1f}" '
                           f'rx="{(x1 - x0) / 2:.1f}" ry="{(y1 - y0) / 2:.1f}" fill="{fill}" '
                           f'stroke="{stroke}" stroke-width="{sw}"/>')
            elif t == "line":
                out.append(f'  <line x1="{co[0]:.1f}" y1="{co[1]:.1f}" x2="{co[2]:.1f}" '
                           f'y2="{co[3]:.1f}" stroke="{stroke}" stroke-width="{sw}" '
                           f'stroke-linecap="round"/>')
            elif t == "pen" and len(co) >= 4:
                pts = " ".join(f"{co[i]:.1f},{co[i + 1]:.1f}" for i in range(0, len(co) - 1, 2))
                out.append(f'  <polyline points="{pts}" fill="none" stroke="{stroke}" '
                           f'stroke-width="{sw}" stroke-linecap="round" stroke-linejoin="round"/>')
            elif t == "text":
                size = s["size"]
                for n, line in enumerate(s["text"].split("\n")):
                    out.append(f'  <text x="{co[0]:.1f}" y="{co[1] + size * (n + 1):.1f}" '
                               f'fill="{stroke}" font-family="Segoe UI, Arial, sans-serif" '
                               f'font-size="{size}">{escape(line)}</text>')
        out.append("</svg>")
        return "\n".join(out) + "\n"

    def show_help(self):
        messagebox.showinfo(APP_NAME, (
            "Ferramentas: V selecionar, R retângulo, E elipse, L linha, P lápis, T texto\n\n"
            "Shift ao desenhar: quadrado/círculo perfeito e linhas a 45°\n"
            "Setas: mover a forma selecionada (Shift+seta move 10 px)\n"
            "Duplo clique em um texto: editar\n"
            "Del: excluir   Ctrl+D: duplicar\n"
            "Ctrl+Z / Ctrl+Y: desfazer / refazer\n"
            "Ctrl+] / Ctrl+[: trazer para frente / enviar para trás\n"
            "Ctrl+S: salvar   Ctrl+O: abrir   Ctrl+E: exportar SVG"
        ), parent=self.root)

    def quit(self):
        if self._confirm_discard():
            self.root.destroy()


def main():
    try:  # deixa a janela nítida em telas de alta resolução no Windows
        from ctypes import windll
        windll.shcore.SetProcessDpiAwareness(1)
    except Exception:  # noqa: BLE001
        pass
    root = tk.Tk()
    root.geometry("1150x720")
    root.minsize(760, 480)
    style = ttk.Style(root)
    if "vista" in style.theme_names():
        style.theme_use("vista")
    VectorApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()

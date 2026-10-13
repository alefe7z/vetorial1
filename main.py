"""Vetorial 2 - editor de desenho vetorial inspirado no CorelDRAW (PySide6 / Qt).

Ferramentas: Seleção, Forma (edição de nós), Zoom, Mão, Mão livre, Caneta (Bézier),
Retângulo, Elipse, Polígono/Estrela e Texto.
Recursos: réguas em mm, página configurável, zoom de 5% a 5000%, paleta de cores
(clique = preenchimento, botão direito = contorno), mover/redimensionar/girar,
alinhar, organizar, espelhar, converter em curvas, desfazer/refazer, área de
transferência, salvar/abrir (.vetorial) e exportar PDF, PNG e SVG.
"""
import copy
import json
import math
import sys
from xml.sax.saxutils import escape

from PySide6.QtCore import QLocale, QMarginsF, QPointF, QRectF, QSize, QSizeF, Qt, QTimer, Signal
from PySide6.QtGui import (QAction, QActionGroup, QColor, QFont, QFontMetricsF, QIcon, QImage,
                           QKeySequence, QPageLayout, QPageSize, QPainter, QPainterPath,
                           QPainterPathStroker, QPalette, QPdfWriter, QPen, QPixmap, QPolygonF,
                           QTransform)
from PySide6.QtWidgets import (QAbstractItemView, QApplication, QCheckBox, QColorDialog, QComboBox,
                               QDockWidget, QDoubleSpinBox, QFileDialog, QFontComboBox, QFrame,
                               QGraphicsItem, QGraphicsScene, QGraphicsView, QGridLayout, QGroupBox,
                               QHBoxLayout, QInputDialog, QLabel, QListWidget, QListWidgetItem,
                               QMainWindow, QMessageBox, QPushButton, QSpinBox, QTabWidget,
                               QToolBar, QToolButton, QVBoxLayout, QWidget)

APP = "Vetorial"
EXT = ".vetorial"
PX_MM = 96 / 25.4          # pixels por milímetro em 100% de zoom
PT_MM = 25.4 / 72          # milímetros por ponto tipográfico
ZOOM_MIN, ZOOM_MAX = 0.05, 50.0
RULER = 22
DESK = 2000                # margem da área de trabalho ao redor da página (mm)
MAX_UNDO = 300

PAGES = {"A3": (297.0, 420.0), "A4": (210.0, 297.0), "A5": (148.0, 210.0),
         "Carta": (215.9, 279.4), "Ofício": (215.9, 355.6)}

PALETTE = [
    "#000000", "#1a1a1a", "#333333", "#4d4d4d", "#666666", "#808080", "#999999", "#b3b3b3",
    "#cccccc", "#e6e6e6", "#ffffff",
    "#e30613", "#e5007e", "#ffed00", "#009fe3", "#2d2e83", "#009640", "#f39200", "#951b81",
    "#8b5a2b",
    "#ff8a80", "#f8bbd0", "#fff59d", "#b3e5fc", "#9fa8da", "#a5d6a7", "#ffcc80", "#ce93d8",
    "#d7ccc8",
    "#7f0000", "#880e4f", "#827717", "#01579b", "#1a237e", "#1b5e20", "#bf360c", "#4a148c",
    "#3e2723",
]

TOOLS = [
    ("pick", "Seleção", "V"),
    ("shape", "Forma (editar nós)", "F10"),
    ("zoom", "Zoom", "Z"),
    ("pan", "Mão (mover a vista)", "H"),
    ("free", "Mão livre", "F5"),
    ("pen", "Caneta (Bézier)", "P"),
    ("rect", "Retângulo", "F6"),
    ("ellipse", "Elipse", "F7"),
    ("polygon", "Polígono / Estrela", "Y"),
    ("text", "Texto", "F8"),
]
TOOL_NAMES = {k: n for k, n, _ in TOOLS}

HINTS = {
    "pick": "Clique para selecionar • Shift+clique soma • Clique de novo no objeto para girar",
    "shape": "Arraste nós e alças • Duplo clique na linha: novo nó • Duplo clique no nó: excluir",
    "zoom": "Clique: aproximar • Botão direito: afastar • Arraste: zoom na área",
    "pan": "Arraste para mover a vista (também: botão do meio ou Espaço)",
    "free": "Arraste para desenhar à mão livre",
    "pen": "Clique: nó de canto • Clique e arraste: curva • Clique no 1º nó: fechar • "
           "Enter/duplo clique: terminar • Backspace: desfaz nó",
    "rect": "Arraste • Ctrl: quadrado • Shift: a partir do centro",
    "ellipse": "Arraste • Ctrl: círculo • Shift: a partir do centro",
    "polygon": "Arraste • Ctrl: proporcional • Shift: a partir do centro",
    "text": "Clique para inserir texto • Clique num texto existente para editar",
}

KIND_NAMES = {"rect": "Retângulo", "ellipse": "Elipse", "path": "Curva", "text": "Texto"}


def fmt(v, d=2):
    return f"{v:.{d}f}".replace(".", ",")


def node(x, y, cin=None, cout=None, smooth=False):
    return {"x": x, "y": y, "in": cin, "out": cout, "smooth": smooth}


# ================================================================ geometria
def seg_ctrl(a, b):
    p0 = (a["x"], a["y"])
    p3 = (b["x"], b["y"])
    p1 = tuple(a["out"]) if a["out"] is not None else p0
    p2 = tuple(b["in"]) if b["in"] is not None else p3
    return p0, p1, p2, p3


def cubic_pt(p0, p1, p2, p3, t):
    mt = 1 - t
    a, b, c, d = mt ** 3, 3 * mt * mt * t, 3 * mt * t * t, t ** 3
    return (a * p0[0] + b * p1[0] + c * p2[0] + d * p3[0],
            a * p0[1] + b * p1[1] + c * p2[1] + d * p3[1])


def split_cubic(p0, p1, p2, p3, t):
    def lerp(u, v):
        return (u[0] + (v[0] - u[0]) * t, u[1] + (v[1] - u[1]) * t)
    a, b, c = lerp(p0, p1), lerp(p1, p2), lerp(p2, p3)
    d, e = lerp(a, b), lerp(b, c)
    m = lerp(d, e)
    return (p0, a, d, m), (m, e, c, p3)


def subpaths_to_qpath(subs, only_closed=False):
    p = QPainterPath()
    for sp in subs:
        nodes = sp["nodes"]
        if not nodes or (only_closed and not sp["closed"]):
            continue
        p.moveTo(nodes[0]["x"], nodes[0]["y"])
        n = len(nodes)
        segs = n if sp["closed"] and n > 1 else n - 1
        for i in range(segs):
            a, b = nodes[i], nodes[(i + 1) % n]
            if a["out"] is None and b["in"] is None:
                p.lineTo(b["x"], b["y"])
            else:
                _, c1, c2, end = seg_ctrl(a, b)
                p.cubicTo(c1[0], c1[1], c2[0], c2[1], end[0], end[1])
        if sp["closed"]:
            p.closeSubpath()
    return p


def qpath_to_subpaths(qp):
    subs, cur, i, n = [], None, 0, qp.elementCount()
    while i < n:
        e = qp.elementAt(i)
        if e.isMoveTo():
            cur = {"nodes": [node(e.x, e.y)], "closed": False}
            subs.append(cur)
            i += 1
        elif e.isLineTo():
            cur["nodes"].append(node(e.x, e.y))
            i += 1
        elif e.isCurveTo():
            c2, end = qp.elementAt(i + 1), qp.elementAt(i + 2)
            cur["nodes"][-1]["out"] = [e.x, e.y]
            cur["nodes"].append(node(end.x, end.y, cin=[c2.x, c2.y]))
            i += 3
        else:
            i += 1
    for sp in subs:
        ns = sp["nodes"]
        if len(ns) > 2 and abs(ns[0]["x"] - ns[-1]["x"]) < 1e-6 and abs(ns[0]["y"] - ns[-1]["y"]) < 1e-6:
            ns[0]["in"] = ns[-1]["in"]
            ns.pop()
            sp["closed"] = True
    return [sp for sp in subs if len(sp["nodes"]) >= 2]


def text_qpath(text, family, size_pt, x, y):
    font = QFont(family)
    font.setPixelSize(100)
    fm = QFontMetricsF(font)
    p = QPainterPath()
    for i, line in enumerate(text.split("\n")):
        if line:
            p.addText(0, fm.ascent() + i * fm.lineSpacing(), font, line)
    s = size_pt * PT_MM / 100
    return QTransform(s, 0, 0, s, x, y).map(p)


def polygon_subpaths(r, sides, star):
    cx, cy = r.center().x(), r.center().y()
    rx, ry = r.width() / 2, r.height() / 2
    count = sides * 2 if star else sides
    pts = []
    for i in range(count):
        a = -math.pi / 2 + i * 2 * math.pi / count
        k = 0.5 if (star and i % 2) else 1.0
        pts.append(node(cx + rx * k * math.cos(a), cy + ry * k * math.sin(a)))
    return [{"nodes": pts, "closed": True}]


def _seg_dist(p, a, b):
    dx, dy = b[0] - a[0], b[1] - a[1]
    L = dx * dx + dy * dy
    if L == 0:
        return math.hypot(p[0] - a[0], p[1] - a[1])
    t = max(0.0, min(1.0, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L))
    return math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy)


def simplify(pts, eps):
    """Ramer-Douglas-Peucker: remove pontos desnecessários do traço à mão livre."""
    if len(pts) < 3:
        return pts
    keep = [False] * len(pts)
    keep[0] = keep[-1] = True
    stack = [(0, len(pts) - 1)]
    while stack:
        i, j = stack.pop()
        dmax, idx = -1.0, -1
        for k in range(i + 1, j):
            d = _seg_dist(pts[k], pts[i], pts[j])
            if d > dmax:
                dmax, idx = d, k
        if dmax > eps:
            keep[idx] = True
            stack += [(i, idx), (idx, j)]
    return [p for p, k in zip(pts, keep) if k]


def smooth_nodes(pts, closed):
    """Converte pontos em nós Bézier suaves (Catmull-Rom)."""
    n, nodes = len(pts), []
    for i, p in enumerate(pts):
        if closed:
            prev, nxt = pts[i - 1], pts[(i + 1) % n]
        else:
            prev, nxt = pts[max(i - 1, 0)], pts[min(i + 1, n - 1)]
        dx, dy = (nxt[0] - prev[0]) / 6, (nxt[1] - prev[1]) / 6
        cin = None if (not closed and i == 0) else [p[0] - dx, p[1] - dy]
        cout = None if (not closed and i == n - 1) else [p[0] + dx, p[1] + dy]
        nodes.append(node(p[0], p[1], cin, cout, smooth=True))
    return nodes


def is_rigid(t):
    a, b, c, d = t.m11(), t.m12(), t.m21(), t.m22()
    return (abs(a * a + b * b - 1) < 1e-6 and abs(c * c + d * d - 1) < 1e-6
            and abs(a * c + b * d) < 1e-6 and (a * d - b * c) > 0)


def T_about(m, p):
    """Aplica a transformação m em torno do ponto p."""
    return QTransform.fromTranslate(-p.x(), -p.y()) * m * QTransform.fromTranslate(p.x(), p.y())


# ================================================================== modelo
FIELDS = ("kind", "x", "y", "w", "h", "radius", "paths", "text", "font", "size",
          "fill", "stroke", "stroke_w", "angle", "tx", "ty")


class Shape:
    def __init__(self, kind, **kw):
        self.kind = kind
        self.x = self.y = self.w = self.h = 0.0
        self.radius = 0.0
        self.paths = []
        self.text, self.font, self.size = "", "Arial", 24.0
        self.fill, self.stroke, self.stroke_w = None, "#000000", 0.2
        self.angle = self.tx = self.ty = 0.0
        self.item = None
        self._cache = self._fcache = None
        for k, v in kw.items():
            setattr(self, k, v)

    def to_dict(self):
        return {k: copy.deepcopy(getattr(self, k)) for k in FIELDS}

    def load(self, d):
        for k in FIELDS:
            if k in d:
                setattr(self, k, copy.deepcopy(d[k]))
        self.invalidate()

    @classmethod
    def from_dict(cls, d):
        s = cls(d["kind"])
        s.load(d)
        return s

    def invalidate(self):
        self._cache = self._fcache = None

    def transform(self):
        t = QTransform()
        t.translate(self.tx, self.ty)
        t.rotate(self.angle)
        return t

    def local_path(self):
        if self._cache is None:
            p = QPainterPath()
            if self.kind == "rect":
                r = QRectF(self.x, self.y, self.w, self.h)
                rr = max(0.0, min(self.radius, abs(self.w) / 2, abs(self.h) / 2))
                if rr > 0:
                    p.addRoundedRect(r, rr, rr)
                else:
                    p.addRect(r)
            elif self.kind == "ellipse":
                p.addEllipse(QRectF(self.x, self.y, self.w, self.h))
            elif self.kind == "path":
                p = subpaths_to_qpath(self.paths)
            elif self.kind == "text":
                p = text_qpath(self.text, self.font, self.size, self.x, self.y)
            self._cache = p
        return self._cache

    def fill_path(self):
        if self.kind != "path":
            return self.local_path()
        if self._fcache is None:
            self._fcache = subpaths_to_qpath(self.paths, only_closed=True)
        return self._fcache

    def scene_bounds(self):
        return self.transform().map(self.local_path()).boundingRect()

    def describe(self):
        if self.kind == "text":
            t = self.text.replace("\n", " ")
            return f"Texto: {t[:24]}{'…' if len(t) > 24 else ''}"
        if self.kind == "path":
            n = sum(len(sp["nodes"]) for sp in self.paths)
            return f"Curva ({n} nós)"
        return KIND_NAMES[self.kind]

    # ----------------------------------------------------- transformações
    def apply(self, M):
        """Aplica uma transformação afim (em coordenadas da cena)."""
        self.invalidate()
        T = self.transform()
        TM = T * M
        if is_rigid(TM):
            self.angle = math.degrees(math.atan2(TM.m12(), TM.m11()))
            self.tx, self.ty = TM.dx(), TM.dy()
            return
        if self.kind == "path":
            self._bake(TM)
            return
        L = T * M * T.inverted()[0]
        if abs(L.m12()) > 1e-9 or abs(L.m21()) > 1e-9:
            self.to_curves()
            self._bake(TM)
            return
        if self.kind in ("rect", "ellipse"):
            r = L.mapRect(QRectF(self.x, self.y, self.w, self.h))
            self.x, self.y, self.w, self.h = r.x(), r.y(), r.width(), r.height()
        elif self.kind == "text":
            b = self.local_path().boundingRect()
            if b.height() > 0:
                nb = L.mapRect(b)
                self.size = max(1.0, self.size * nb.height() / b.height())
                self.invalidate()
                b2 = self.local_path().boundingRect()
                self.x += nb.x() - b2.x()
                self.y += nb.y() - b2.y()
        self.invalidate()

    def _bake(self, TM):
        for sp in self.paths:
            for n in sp["nodes"]:
                p = TM.map(QPointF(n["x"], n["y"]))
                n["x"], n["y"] = p.x(), p.y()
                for k in ("in", "out"):
                    if n[k] is not None:
                        q = TM.map(QPointF(n[k][0], n[k][1]))
                        n[k] = [q.x(), q.y()]
        self.angle = self.tx = self.ty = 0.0
        self.invalidate()

    def to_curves(self):
        if self.kind == "path":
            return
        self.paths = qpath_to_subpaths(self.local_path())
        self.kind = "path"
        self.invalidate()


class ShapeItem(QGraphicsItem):
    def __init__(self, shape):
        super().__init__()
        self.s = shape
        shape.item = self
        self._br = QRectF()
        self.sync()

    def sync(self):
        self.prepareGeometryChange()
        self.s.invalidate()
        self.setTransform(self.s.transform())
        pad = (self.s.stroke_w if self.s.stroke else 0) * 2 + 0.5
        self._br = self.s.local_path().controlPointRect().adjusted(-pad, -pad, pad, pad)
        self.update()

    def boundingRect(self):
        return self._br

    def paint(self, painter, option, widget=None):
        s = self.s
        if s.fill:
            painter.fillPath(s.fill_path(), QColor(s.fill))
        if s.stroke and s.stroke_w > 0:
            pen = QPen(QColor(s.stroke), s.stroke_w)
            pen.setJoinStyle(Qt.PenJoinStyle.MiterJoin)
            pen.setCapStyle(Qt.PenCapStyle.FlatCap)
            painter.strokePath(s.local_path(), pen)


# ================================================================== ícones
def make_icon(name, color="#e8e8e8"):
    pm = QPixmap(28, 28)
    pm.fill(Qt.GlobalColor.transparent)
    p = QPainter(pm)
    p.setRenderHint(QPainter.RenderHint.Antialiasing)
    c = QColor(color)
    pen = QPen(c, 1.6)
    pen.setJoinStyle(Qt.PenJoinStyle.RoundJoin)
    p.setPen(pen)
    p.setBrush(Qt.BrushStyle.NoBrush)

    def node_sq(x, y):
        p.save()
        p.setPen(QPen(c, 1))
        p.setBrush(QColor("#1e1e1e"))
        p.drawRect(QRectF(x - 2.5, y - 2.5, 5, 5))
        p.restore()

    if name == "pick":
        p.setBrush(c)
        p.drawPolygon(QPolygonF([QPointF(8, 4), QPointF(8, 22), QPointF(12.5, 17.5), QPointF(16, 24.5),
                                 QPointF(18.5, 23.3), QPointF(15, 16.5), QPointF(21, 16.5)]))
    elif name == "shape":
        path = QPainterPath(QPointF(4, 22))
        path.cubicTo(8, 6, 18, 6, 24, 12)
        p.drawPath(path)
        p.setPen(QPen(c, 1))
        p.drawLine(QPointF(4, 22), QPointF(6, 10))
        p.setBrush(c)
        p.drawEllipse(QPointF(6, 10), 2, 2)
        node_sq(4, 22)
        node_sq(24, 12)
    elif name in ("zoom", "zoom_in", "zoom_out"):
        p.drawEllipse(QPointF(12, 12), 7, 7)
        thick = QPen(c, 3)
        thick.setCapStyle(Qt.PenCapStyle.RoundCap)
        p.setPen(thick)
        p.drawLine(QPointF(17.5, 17.5), QPointF(24, 24))
        p.setPen(QPen(c, 1.6))
        if name != "zoom":
            p.drawLine(QPointF(8.5, 12), QPointF(15.5, 12))
            if name == "zoom_in":
                p.drawLine(QPointF(12, 8.5), QPointF(12, 15.5))
    elif name == "pan":
        p.drawLine(QPointF(14, 3), QPointF(14, 25))
        p.drawLine(QPointF(3, 14), QPointF(25, 14))
        for a, b, cc in (((11, 6), (17, 6), (14, 3)), ((11, 22), (17, 22), (14, 25)),
                         ((6, 11), (6, 17), (3, 14)), ((22, 11), (22, 17), (25, 14))):
            p.drawPolyline(QPolygonF([QPointF(*a), QPointF(*cc), QPointF(*b)]))
    elif name == "free":
        path = QPainterPath(QPointF(3, 18))
        path.cubicTo(7, 4, 11, 26, 15, 14)
        path.cubicTo(18, 6, 22, 10, 25, 8)
        p.drawPath(path)
    elif name == "pen":
        p.setBrush(c)
        p.drawPolygon(QPolygonF([QPointF(14, 3), QPointF(21, 15), QPointF(16, 25),
                                 QPointF(12, 25), QPointF(7, 15)]))
        p.setPen(QPen(QColor("#1e1e1e"), 1.4))
        p.drawLine(QPointF(14, 8), QPointF(14, 17))
        p.setBrush(QColor("#1e1e1e"))
        p.drawEllipse(QPointF(14, 18), 1.6, 1.6)
    elif name == "rect":
        p.drawRect(QRectF(5, 7, 18, 14))
    elif name == "ellipse":
        p.drawEllipse(QRectF(4, 7, 20, 14))
    elif name == "polygon":
        pts = [QPointF(14 + 10 * math.cos(-math.pi / 2 + i * 2 * math.pi / 5),
                       15 + 10 * math.sin(-math.pi / 2 + i * 2 * math.pi / 5)) for i in range(5)]
        p.drawPolygon(QPolygonF(pts))
    elif name == "text":
        f = QFont("Arial")
        f.setPixelSize(20)
        f.setBold(True)
        p.setFont(f)
        p.drawText(QRectF(0, 0, 28, 28), Qt.AlignmentFlag.AlignCenter, "A")
    elif name == "page":
        p.drawRect(QRectF(7, 4, 14, 20))
        p.setPen(QPen(c, 1.2))
        for x, y, dx, dy in ((3, 3, 1, 0), (3, 3, 0, 1), (25, 25, -1, 0), (25, 25, 0, -1)):
            p.drawLine(QPointF(x, y), QPointF(x + dx * 4, y + dy * 4))
    elif name == "new":
        p.drawPolygon(QPolygonF([QPointF(7, 3), QPointF(17, 3), QPointF(22, 8), QPointF(22, 25),
                                 QPointF(7, 25)]))
        p.drawPolyline(QPolygonF([QPointF(17, 3), QPointF(17, 8), QPointF(22, 8)]))
    elif name == "open":
        p.drawPolygon(QPolygonF([QPointF(3, 8), QPointF(10, 8), QPointF(12, 10), QPointF(23, 10),
                                 QPointF(23, 22), QPointF(3, 22)]))
        p.drawLine(QPointF(3, 13), QPointF(23, 13))
    elif name == "save":
        p.drawRect(QRectF(4, 4, 20, 20))
        p.drawRect(QRectF(9, 4, 10, 7))
        p.drawRect(QRectF(8, 15, 12, 9))
    elif name == "export":
        p.drawPolyline(QPolygonF([QPointF(5, 15), QPointF(5, 24), QPointF(23, 24), QPointF(23, 15)]))
        p.drawLine(QPointF(14, 4), QPointF(14, 18))
        p.drawPolyline(QPolygonF([QPointF(9, 9), QPointF(14, 4), QPointF(19, 9)]))
    elif name in ("undo", "redo"):
        if name == "redo":
            p.translate(28, 0)
            p.scale(-1, 1)
        path = QPainterPath(QPointF(7, 12))
        path.cubicTo(12, 6, 24, 8, 22, 21)
        p.drawPath(path)
        p.drawPolyline(QPolygonF([QPointF(6, 6), QPointF(7, 12), QPointF(13, 13)]))
    p.end()
    return QIcon(pm)


# ================================================================== réguas
class Ruler(QWidget):
    def __init__(self, canvas, horizontal):
        super().__init__()
        self.c = canvas
        self.h = horizontal
        if horizontal:
            self.setFixedHeight(RULER)
        else:
            self.setFixedWidth(RULER)

    def paintEvent(self, ev):
        p = QPainter(self)
        p.fillRect(self.rect(), QColor("#262626"))
        k = self.c.scale_px()
        steps = [0.1, 0.2, 0.5, 1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000, 5000]
        major = next((s for s in steps if s * k >= 60), steps[-1])
        minor = major / 10 if major * k / 10 >= 5 else (major / 5 if major * k / 5 >= 5 else major / 2)
        vt = self.c.viewportTransform()
        inv = vt.inverted()[0]
        length = self.width() if self.h else self.height()
        a = inv.map(QPointF(0, 0))
        b = inv.map(QPointF(length, length))
        lo, hi = (a.x(), b.x()) if self.h else (a.y(), b.y())
        f = QFont()
        f.setPixelSize(9)
        p.setFont(f)
        p.setPen(QColor("#9a9a9a"))
        i0 = math.floor(lo / minor)
        i = i0
        decimals = 1 if major < 1 else 0
        while True:
            v = i * minor
            if v > hi:
                break
            pos = vt.map(QPointF(v, v))
            pos = pos.x() if self.h else pos.y()
            is_major = abs(v / major - round(v / major)) < 1e-6
            tick = 10 if is_major else (6 if abs(v / (major / 2) - round(v / (major / 2))) < 1e-6 else 3)
            if self.h:
                p.drawLine(QPointF(pos, RULER), QPointF(pos, RULER - tick))
                if is_major:
                    p.drawText(QPointF(pos + 2, 10), f"{v:.{decimals}f}".replace(".", ","))
            else:
                p.drawLine(QPointF(RULER, pos), QPointF(RULER - tick, pos))
                if is_major:
                    p.save()
                    p.translate(10, pos - 2)
                    p.rotate(-90)
                    p.drawText(QPointF(0, 0), f"{v:.{decimals}f}".replace(".", ","))
                    p.restore()
            i += 1
            if i - i0 > 2000:
                break
        m = vt.map(self.c.mouse_scene)
        p.setPen(QColor("#4aa3ff"))
        if self.h:
            p.drawLine(QPointF(m.x(), 0), QPointF(m.x(), RULER))
        else:
            p.drawLine(QPointF(0, m.y()), QPointF(RULER, m.y()))
        p.setPen(QColor("#3a3a3a"))
        if self.h:
            p.drawLine(0, RULER - 1, self.width(), RULER - 1)
        else:
            p.drawLine(RULER - 1, 0, RULER - 1, self.height())


# ================================================================== paleta
class PaletteBar(QWidget):
    colorClicked = Signal(object, bool)   # cor (ou None) / True se for contorno
    CELL = 16
    COLS = 2

    def __init__(self):
        super().__init__()
        self.colors = [None] + PALETTE
        rows = math.ceil(len(self.colors) / self.COLS)
        self.setFixedSize(self.COLS * self.CELL + 4, rows * self.CELL + 4)
        self.setToolTip("Clique: preenchimento\nBotão direito: contorno\nX: nenhum")

    def _rect(self, i):
        return QRectF(2 + (i % self.COLS) * self.CELL, 2 + (i // self.COLS) * self.CELL,
                      self.CELL - 1, self.CELL - 1)

    def paintEvent(self, ev):
        p = QPainter(self)
        for i, c in enumerate(self.colors):
            r = self._rect(i)
            if c is None:
                p.fillRect(r, QColor("white"))
                p.setPen(QPen(QColor("#e30613"), 1.5))
                p.drawLine(r.topLeft(), r.bottomRight())
                p.drawLine(r.topRight(), r.bottomLeft())
            else:
                p.fillRect(r, QColor(c))
            p.setPen(QColor("#111"))
            p.drawRect(r)

    def mousePressEvent(self, e):
        for i in range(len(self.colors)):
            if self._rect(i).contains(e.position()):
                self.colorClicked.emit(self.colors[i], e.button() == Qt.MouseButton.RightButton)
                return


# ================================================================== tela
class Canvas(QGraphicsView):
    zoomChanged = Signal(float)
    mouseMoved = Signal(QPointF)

    def __init__(self, win):
        super().__init__(win.scene)
        self.win = win
        self.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.TextAntialiasing
                            | QPainter.RenderHint.SmoothPixmapTransform)
        self.setTransformationAnchor(QGraphicsView.ViewportAnchor.NoAnchor)
        self.setResizeAnchor(QGraphicsView.ViewportAnchor.AnchorViewCenter)
        self.setViewportUpdateMode(QGraphicsView.ViewportUpdateMode.FullViewportUpdate)
        self.setFrameShape(QFrame.Shape.NoFrame)
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.FocusPolicy.StrongFocus)
        self.tool = "pick"
        self.drag = None
        self.rotate_mode = False
        self.pan_last = None
        self.space = False
        self.pen_nodes = []
        self.pen_dragging = False
        self.pen_press = QPointF()
        self.free_pts = []
        self.edit = None
        self.node_sel = None
        self.mouse_scene = QPointF()
        self.scale(PX_MM, PX_MM)
        self.handlers = {
            "pick": (self.press_pick, self.move_pick, self.release_pick),
            "shape": (self.press_shape, self.move_shape, self.release_shape),
            "zoom": (self.press_zoom, self.move_zoom, self.release_zoom),
            "pan": (None, None, None),
            "free": (self.press_free, self.move_free, self.release_free),
            "pen": (self.press_pen, self.move_pen, self.release_pen),
            "rect": (self.press_create, self.move_create, self.release_create),
            "ellipse": (self.press_create, self.move_create, self.release_create),
            "polygon": (self.press_create, self.move_create, self.release_create),
            "text": (self.press_text, None, None),
        }

    # -------------------------------------------------------- utilidades
    def scale_px(self):
        return self.transform().m11()

    def zoom_pct(self):
        return self.scale_px() / PX_MM * 100

    def to_scene(self, vp):
        return self.viewportTransform().inverted()[0].map(QPointF(vp))

    def to_view(self, sp):
        return self.viewportTransform().map(QPointF(sp))

    def near(self, sp, vp, tol=6):
        v = self.to_view(sp)
        return abs(v.x() - vp.x()) <= tol and abs(v.y() - vp.y()) <= tol

    def cpen(self, color, width=1.0, dash=False):
        pen = QPen(QColor(color), width)
        pen.setCosmetic(True)
        if dash:
            pen.setStyle(Qt.PenStyle.DashLine)
        return pen

    def apply_cursor(self):
        cur = {"pick": Qt.CursorShape.ArrowCursor, "shape": Qt.CursorShape.PointingHandCursor,
               "pan": Qt.CursorShape.OpenHandCursor, "text": Qt.CursorShape.IBeamCursor}
        self.viewport().setCursor(cur.get(self.tool, Qt.CursorShape.CrossCursor))

    # -------------------------------------------------------------- zoom
    def zoom_at(self, factor, vp=None):
        if vp is None:
            vp = QPointF(self.viewport().rect().center())
        cur = self.scale_px()
        new = min(max(cur * factor, ZOOM_MIN * PX_MM), ZOOM_MAX * PX_MM)
        f = new / cur
        if abs(f - 1) < 1e-9:
            return
        before = self.to_scene(vp)
        self.scale(f, f)
        d = self.to_view(before) - QPointF(vp)
        h, v = self.horizontalScrollBar(), self.verticalScrollBar()
        h.setValue(h.value() + round(d.x()))
        v.setValue(v.value() + round(d.y()))
        self.zoomChanged.emit(self.zoom_pct())

    def set_zoom_pct(self, pct):
        c = self.to_scene(QPointF(self.viewport().rect().center()))
        s = min(max(pct / 100, ZOOM_MIN), ZOOM_MAX) * PX_MM
        self.setTransform(QTransform.fromScale(s, s))
        self.centerOn(c)
        self.zoomChanged.emit(self.zoom_pct())

    def zoom_to_rect(self, r, margin=0.06):
        vw, vh = self.viewport().width(), self.viewport().height()
        w = max(r.width(), 1e-6) * (1 + 2 * margin)
        h = max(r.height(), 1e-6) * (1 + 2 * margin)
        s = min(vw / w, vh / h)
        s = min(max(s, ZOOM_MIN * PX_MM), ZOOM_MAX * PX_MM)
        self.setTransform(QTransform.fromScale(s, s))
        self.centerOn(r.center())
        self.zoomChanged.emit(self.zoom_pct())

    def zoom_page(self):
        self.zoom_to_rect(QRectF(0, 0, self.win.page_w, self.win.page_h), 0.04)

    def zoom_objects(self):
        if self.win.shapes:
            r = QRectF()
            for s in self.win.shapes:
                r = r.united(s.scene_bounds())
            self.zoom_to_rect(r)

    def zoom_selection(self):
        if self.win.selection:
            self.zoom_to_rect(self.win.selection_bounds())

    def wheelEvent(self, e):
        dy = e.angleDelta().y()
        mods = e.modifiers()
        if mods & Qt.KeyboardModifier.ControlModifier:
            self.verticalScrollBar().setValue(self.verticalScrollBar().value() - dy)
        elif mods & Qt.KeyboardModifier.ShiftModifier:
            self.horizontalScrollBar().setValue(self.horizontalScrollBar().value() - dy)
        elif dy:
            self.zoom_at(1.2 ** (dy / 120), e.position())
        e.accept()

    # --------------------------------------------------------- desenhar
    def drawBackground(self, painter, rect):
        painter.fillRect(rect, QColor("#ececec"))
        w, h = self.win.page_w, self.win.page_h
        k = 1 / self.scale_px()
        painter.fillRect(QRectF(4 * k, 4 * k, w, h), QColor(0, 0, 0, 60))
        painter.fillRect(QRectF(0, 0, w, h), QColor("white"))
        painter.setPen(self.cpen("#6b6b6b"))
        painter.setBrush(Qt.BrushStyle.NoBrush)
        painter.drawRect(QRectF(0, 0, w, h))

    def drawForeground(self, painter, rect):
        k = 1 / self.scale_px()
        win = self.win
        painter.setBrush(Qt.BrushStyle.NoBrush)

        def square(p, size=7, fill="#000000", border="#ffffff"):
            painter.setPen(self.cpen(border))
            painter.setBrush(QColor(fill))
            painter.drawRect(QRectF(p.x() - size / 2 * k, p.y() - size / 2 * k, size * k, size * k))
            painter.setBrush(Qt.BrushStyle.NoBrush)

        def circle(p, size=7, fill="#ffffff", border="#1e6fd9"):
            painter.setPen(self.cpen(border))
            painter.setBrush(QColor(fill))
            painter.drawEllipse(p, size / 2 * k, size / 2 * k)
            painter.setBrush(Qt.BrushStyle.NoBrush)

        if self.tool == "pick" and win.selection:
            r = win.selection_bounds()
            re = self.handle_rect(r)
            painter.setPen(self.cpen("#1e6fd9", 1, dash=True))
            painter.drawRect(r)
            pts = self.handle_points(re)
            if self.rotate_mode:
                for i, p in enumerate(pts):
                    if i % 2 == 0:
                        circle(p, 9, "#ffffff", "#000000")
                c = r.center()
                painter.setPen(self.cpen("#000000"))
                painter.drawEllipse(c, 4 * k, 4 * k)
                painter.drawLine(QPointF(c.x() - 2 * k, c.y()), QPointF(c.x() + 2 * k, c.y()))
            else:
                for p in pts:
                    square(p)
                c = r.center()
                painter.setPen(self.cpen("#000000", 1.5))
                painter.drawLine(QPointF(c.x() - 3 * k, c.y() - 3 * k), QPointF(c.x() + 3 * k, c.y() + 3 * k))
                painter.drawLine(QPointF(c.x() - 3 * k, c.y() + 3 * k), QPointF(c.x() + 3 * k, c.y() - 3 * k))

        if self.tool == "shape" and self.edit is not None and self.edit in win.shapes:
            s = self.edit
            T = s.transform()
            painter.setPen(self.cpen("#1e6fd9"))
            painter.drawPath(T.map(s.local_path()))
            if s.kind == "path":
                for key, si, ni, pt in self.visible_handles(s):
                    n = s.paths[si]["nodes"][ni]
                    a, b = T.map(QPointF(n["x"], n["y"])), T.map(QPointF(*pt))
                    painter.setPen(self.cpen("#1e6fd9", 1, dash=True))
                    painter.drawLine(a, b)
                    circle(b, 10, "#1e6fd9", "#ffffff")
                for si, sp in enumerate(s.paths):
                    for ni, n in enumerate(sp["nodes"]):
                        p = T.map(QPointF(n["x"], n["y"]))
                        sel = self.node_sel == (si, ni)
                        size = 10 if (si == 0 and ni == 0) else 8
                        square(p, size, "#1e6fd9" if sel else "#ffffff", "#000000")

        if self.tool == "pen" and self.pen_nodes:
            path = subpaths_to_qpath([{"nodes": self.pen_nodes, "closed": False}])
            last = self.pen_nodes[-1]
            m = self.mouse_scene
            if not self.pen_dragging:
                if last["out"] is not None:
                    path.cubicTo(last["out"][0], last["out"][1], m.x(), m.y(), m.x(), m.y())
                else:
                    path.lineTo(m)
            painter.setPen(self.cpen("#000000", 1))
            painter.drawPath(path)
            for k2 in ("in", "out"):
                if last[k2] is not None:
                    hp = QPointF(*last[k2])
                    painter.setPen(self.cpen("#1e6fd9", 1, dash=True))
                    painter.drawLine(QPointF(last["x"], last["y"]), hp)
                    circle(hp, 10, "#1e6fd9", "#ffffff")
            for i, n in enumerate(self.pen_nodes):
                square(QPointF(n["x"], n["y"]), 8, "#ffffff", "#000000")
            f = self.pen_nodes[0]
            if len(self.pen_nodes) >= 2 and self.near(QPointF(f["x"], f["y"]), self.to_view(m), 7):
                painter.setPen(self.cpen("#e30613", 2))
                painter.drawEllipse(QPointF(f["x"], f["y"]), 7 * k, 7 * k)

        if self.tool == "free" and len(self.free_pts) > 1:
            painter.setPen(self.cpen("#000000", 1))
            painter.drawPolyline(QPolygonF([QPointF(*p) for p in self.free_pts]))

        if self.drag and self.drag.get("op") in ("marquee", "zoomrect"):
            painter.setPen(self.cpen("#1e6fd9", 1, dash=True))
            painter.setBrush(QColor(30, 111, 217, 25))
            painter.drawRect(QRectF(self.drag["start"], self.drag["cur"]).normalized())

    # ------------------------------------------------- testes de clique
    def hit_test(self, sp):
        tol = 4 / self.scale_px()
        for s in reversed(self.win.shapes):
            if self.shape_hit(s, sp, tol):
                return s
        return None

    def shape_hit(self, s, sp, tol):
        lp = s.transform().inverted()[0].map(sp)
        path = s.local_path()
        sw = s.stroke_w if s.stroke else 0
        if not path.controlPointRect().adjusted(-tol - sw, -tol - sw, tol + sw, tol + sw).contains(lp):
            return False
        if s.kind == "text":
            return path.boundingRect().adjusted(-tol, -tol, tol, tol).contains(lp)
        if s.fill and s.fill_path().contains(lp):
            return True
        st = QPainterPathStroker()
        st.setWidth(sw + 2 * tol)
        return st.createStroke(path).contains(lp)

    def handle_rect(self, r):
        m = 5 / self.scale_px()
        return r.adjusted(-m, -m, m, m)

    @staticmethod
    def handle_points(r):
        cx, cy = r.center().x(), r.center().y()
        return [r.topLeft(), QPointF(cx, r.top()), r.topRight(), QPointF(r.right(), cy),
                r.bottomRight(), QPointF(cx, r.bottom()), r.bottomLeft(), QPointF(r.left(), cy)]

    def handle_at(self, vp):
        if self.tool != "pick" or not self.win.selection:
            return None
        pts = self.handle_points(self.handle_rect(self.win.selection_bounds()))
        for i, p in enumerate(pts):
            if self.rotate_mode and i % 2 == 1:
                continue
            if self.near(p, vp):
                return i
        return None

    def visible_handles(self, s):
        if self.node_sel is None:
            return []
        si, ni = self.node_sel
        if si >= len(s.paths) or ni >= len(s.paths[si]["nodes"]):
            self.node_sel = None
            return []
        sub = s.paths[si]
        nodes, n, closed = sub["nodes"], len(sub["nodes"]), sub["closed"]
        out = []
        cur = nodes[ni]
        for key in ("in", "out"):
            if cur[key] is not None:
                out.append((key, si, ni, cur[key]))
        if ni > 0 or closed:
            pi = (ni - 1) % n
            if nodes[pi]["out"] is not None and pi != ni:
                out.append(("out", si, pi, nodes[pi]["out"]))
        if ni < n - 1 or closed:
            nx = (ni + 1) % n
            if nodes[nx]["in"] is not None and nx != ni:
                out.append(("in", si, nx, nodes[nx]["in"]))
        return out

    def node_hit(self, s, vp):
        T = s.transform()
        for key, si, ni, pt in self.visible_handles(s):
            if self.near(T.map(QPointF(*pt)), vp):
                return key, si, ni
        for si, sp in enumerate(s.paths):
            for ni, n in enumerate(sp["nodes"]):
                if self.near(T.map(QPointF(n["x"], n["y"])), vp):
                    return "node", si, ni
        return None

    def segment_hit(self, s, vp):
        T = s.transform()
        best = None
        for si, sp in enumerate(s.paths):
            nodes = sp["nodes"]
            n = len(nodes)
            segs = n if sp["closed"] and n > 1 else n - 1
            for i in range(segs):
                ctrl = seg_ctrl(nodes[i], nodes[(i + 1) % n])
                for j in range(1, 60):
                    t = j / 60
                    q = cubic_pt(*ctrl, t)
                    v = self.to_view(T.map(QPointF(*q)))
                    d = math.hypot(v.x() - vp.x(), v.y() - vp.y())
                    if d <= 6 and (best is None or d < best[0]):
                        best = (d, si, i, t)
        return None if best is None else best[1:]

    # ------------------------------------------------------------ mouse
    def mousePressEvent(self, e):
        self.setFocus()
        vp = e.position()
        sp = self.to_scene(vp)
        btn = e.button()
        if btn == Qt.MouseButton.MiddleButton or (btn == Qt.MouseButton.LeftButton and (self.space or self.tool == "pan")):
            self.pan_last = vp
            self.viewport().setCursor(Qt.CursorShape.ClosedHandCursor)
            return
        if btn == Qt.MouseButton.RightButton:
            if self.tool == "zoom":
                self.zoom_at(0.5, vp)
            elif self.tool == "pen":
                self.finish_pen()
            return
        if btn != Qt.MouseButton.LeftButton:
            return
        h = self.handlers[self.tool][0]
        if h:
            h(e, vp, sp)
        self.viewport().update()

    def mouseMoveEvent(self, e):
        vp = e.position()
        sp = self.to_scene(vp)
        self.mouse_scene = sp
        self.mouseMoved.emit(sp)
        if self.pan_last is not None:
            d = vp - self.pan_last
            self.pan_last = vp
            h, v = self.horizontalScrollBar(), self.verticalScrollBar()
            h.setValue(h.value() - round(d.x()))
            v.setValue(v.value() - round(d.y()))
            return
        h = self.handlers[self.tool][1]
        if h:
            h(e, vp, sp)
        self.viewport().update()

    def mouseReleaseEvent(self, e):
        vp = e.position()
        sp = self.to_scene(vp)
        if self.pan_last is not None:
            self.pan_last = None
            self.apply_cursor()
            if self.space:
                self.viewport().setCursor(Qt.CursorShape.OpenHandCursor)
            return
        if e.button() != Qt.MouseButton.LeftButton:
            return
        h = self.handlers[self.tool][2]
        if h:
            h(e, vp, sp)
        self.viewport().update()

    def mouseDoubleClickEvent(self, e):
        if e.button() != Qt.MouseButton.LeftButton or self.space:
            return self.mousePressEvent(e)
        vp = e.position()
        sp = self.to_scene(vp)
        if self.tool == "pick":
            hit = self.hit_test(sp)
            if hit is not None and hit.kind == "text":
                self.drag = None
                self.win.edit_text(hit)
                return
            if hit is not None and hit.kind == "path":
                self.drag = None
                self.win.set_selection([hit])
                self.win.set_tool("shape")
                return
        elif self.tool == "pen":
            self.finish_pen()
            return
        elif self.tool == "shape":
            if self.double_shape(vp, sp):
                return
        self.mousePressEvent(e)

    # ---------------------------------------------------------- seleção
    def press_pick(self, e, vp, sp):
        w = self.win
        shift = bool(e.modifiers() & Qt.KeyboardModifier.ShiftModifier)
        h = self.handle_at(vp)
        if h is not None:
            self.drag = {"op": "rotate" if self.rotate_mode else "scale", "h": h,
                         "r": w.selection_bounds(), "start": sp,
                         "orig": [s.to_dict() for s in w.selection], "before": w.snapshot()}
            return
        hit = self.hit_test(sp)
        if hit is None:
            if not shift:
                w.set_selection([])
            self.drag = {"op": "marquee", "start": sp, "cur": sp, "add": shift}
            return
        was = hit in w.selection
        if shift:
            sel = list(w.selection)
            if was:
                sel.remove(hit)
            else:
                sel.append(hit)
            w.set_selection(sel)
            if hit not in w.selection:
                self.drag = None
                return
        elif not was:
            w.set_selection([hit])
        self.drag = {"op": "move", "start": sp, "vstart": QPointF(vp),
                     "orig": [s.to_dict() for s in w.selection], "before": w.snapshot(),
                     "moved": False, "toggle": was and not shift}

    def _apply_drag(self, M):
        for s, o in zip(self.win.selection, self.drag["orig"]):
            s.load(o)
            s.apply(M)
            self.win.sync(s)
        self.win.refresh_props()

    def move_pick(self, e, vp, sp):
        d = self.drag
        mods = e.modifiers()
        ctrl = bool(mods & Qt.KeyboardModifier.ControlModifier)
        if d is None:
            h = self.handle_at(vp)
            if h is not None:
                if self.rotate_mode:
                    cur = Qt.CursorShape.CrossCursor
                else:
                    cur = [Qt.CursorShape.SizeFDiagCursor, Qt.CursorShape.SizeVerCursor,
                           Qt.CursorShape.SizeBDiagCursor, Qt.CursorShape.SizeHorCursor][h % 4]
            elif self.hit_test(sp) is not None:
                cur = Qt.CursorShape.SizeAllCursor
            else:
                cur = Qt.CursorShape.ArrowCursor
            self.viewport().setCursor(cur)
            return
        if d["op"] == "marquee":
            d["cur"] = sp
        elif d["op"] == "move":
            if not d["moved"]:
                if abs(vp.x() - d["vstart"].x()) < 3 and abs(vp.y() - d["vstart"].y()) < 3:
                    return
                d["moved"] = True
            dx, dy = sp.x() - d["start"].x(), sp.y() - d["start"].y()
            if ctrl:
                if abs(dx) > abs(dy):
                    dy = 0
                else:
                    dx = 0
            self._apply_drag(QTransform.fromTranslate(dx, dy))
        elif d["op"] == "scale":
            self._apply_drag(self.scale_matrix(d, sp, mods))
        elif d["op"] == "rotate":
            c = d["r"].center()
            a0 = math.atan2(d["start"].y() - c.y(), d["start"].x() - c.x())
            a1 = math.atan2(sp.y() - c.y(), sp.x() - c.x())
            ang = math.degrees(a1 - a0)
            if ctrl:
                ang = round(ang / 15) * 15
            self._apply_drag(T_about(QTransform().rotate(ang), c))

    def scale_matrix(self, d, sp, mods):
        r, h = d["r"], d["h"]
        pts = self.handle_points(r)
        anchor = r.center() if mods & Qt.KeyboardModifier.ShiftModifier else pts[(h + 4) % 8]
        hp = pts[h]

        def factor(cur, a, orig):
            den = orig - a
            return 1.0 if abs(den) < 1e-9 else (cur - a) / den

        sx = factor(sp.x(), anchor.x(), hp.x()) if h not in (1, 5) else 1.0
        sy = factor(sp.y(), anchor.y(), hp.y()) if h not in (3, 7) else 1.0
        if h % 2 == 0 and not (mods & Qt.KeyboardModifier.ControlModifier):
            s = max(abs(sx), abs(sy))
            sx, sy = math.copysign(s, sx), math.copysign(s, sy)
        sx = sx if abs(sx) > 1e-3 else math.copysign(1e-3, sx or 1)
        sy = sy if abs(sy) > 1e-3 else math.copysign(1e-3, sy or 1)
        return T_about(QTransform.fromScale(sx, sy), anchor)

    def release_pick(self, e, vp, sp):
        d, self.drag = self.drag, None
        w = self.win
        if not d:
            return
        if d["op"] == "marquee":
            r = QRectF(d["start"], d["cur"]).normalized()
            if r.width() * self.scale_px() > 2 or r.height() * self.scale_px() > 2:
                inside = []
                for s in w.shapes:
                    b = s.scene_bounds()
                    if r.contains(b.topLeft()) and r.contains(b.bottomRight()):
                        inside.append(s)
                sel = list(w.selection) + [s for s in inside if s not in w.selection] if d["add"] else inside
                w.set_selection(sel)
        elif d["op"] == "move" and not d["moved"]:
            if d["toggle"]:
                self.rotate_mode = not self.rotate_mode
        else:
            w.commit(d["before"])

    # ------------------------------------------------------ ferramenta forma
    def press_shape(self, e, vp, sp):
        w = self.win
        s = self.edit
        if s is not None and s in w.shapes and s.kind == "path":
            hit = self.node_hit(s, vp)
            if hit:
                key, si, ni = hit
                if key == "node":
                    self.node_sel = (si, ni)
                self.drag = {"op": key, "si": si, "ni": ni, "before": w.snapshot(), "start": sp,
                             "orig": copy.deepcopy(s.paths), "moved": False}
                w.refresh_props()
                return
        hit = self.hit_test(sp)
        if hit is not None:
            if hit is not self.edit:
                self.node_sel = None
            self.edit = hit
            w.set_selection([hit])
            if hit.kind != "path":
                w.statusBar().showMessage(
                    "Para editar os nós, converta em curvas: Objeto → Converter em curvas (Ctrl+Q)", 5000)
        else:
            self.edit = None
            self.node_sel = None
            w.set_selection([])

    def move_shape(self, e, vp, sp):
        d, s = self.drag, self.edit
        if d is None or s is None:
            return
        inv = s.transform().inverted()[0]
        lp, l0 = inv.map(sp), inv.map(d["start"])
        dx, dy = lp.x() - l0.x(), lp.y() - l0.y()
        s.paths = copy.deepcopy(d["orig"])
        n = s.paths[d["si"]]["nodes"][d["ni"]]
        if d["op"] == "node":
            n["x"] += dx
            n["y"] += dy
            for k in ("in", "out"):
                if n[k] is not None:
                    n[k] = [n[k][0] + dx, n[k][1] + dy]
        else:
            key = d["op"]
            n[key] = [n[key][0] + dx, n[key][1] + dy]
            other = "out" if key == "in" else "in"
            if n["smooth"] and n[other] is not None:
                vx, vy = n[key][0] - n["x"], n[key][1] - n["y"]
                L = math.hypot(vx, vy)
                ol = math.hypot(n[other][0] - n["x"], n[other][1] - n["y"])
                if L > 1e-9:
                    n[other] = [n["x"] - vx / L * ol, n["y"] - vy / L * ol]
        d["moved"] = True
        self.win.sync(s)
        self.win.refresh_props()

    def release_shape(self, e, vp, sp):
        d, self.drag = self.drag, None
        if d and d.get("moved"):
            self.win.commit(d["before"])

    def double_shape(self, vp, sp):
        s, w = self.edit, self.win
        if s is None or s not in w.shapes or s.kind != "path":
            return False
        hit = self.node_hit(s, vp)
        if hit and hit[0] == "node":
            self.node_sel = (hit[1], hit[2])
            w.delete_node()
            return True
        seg = self.segment_hit(s, vp)
        if seg:
            before = w.snapshot()
            si, i, t = seg
            nodes = s.paths[si]["nodes"]
            a, b = nodes[i], nodes[(i + 1) % len(nodes)]
            if a["out"] is None and b["in"] is None:
                new = node(a["x"] + (b["x"] - a["x"]) * t, a["y"] + (b["y"] - a["y"]) * t)
            else:
                left, right = split_cubic(*seg_ctrl(a, b), t)
                a["out"] = list(left[1])
                b["in"] = list(right[2])
                new = node(left[3][0], left[3][1], list(left[2]), list(right[1]), smooth=True)
            nodes.insert(i + 1, new)
            self.node_sel = (si, i + 1)
            w.sync(s)
            w.commit(before)
            return True
        return False

    # -------------------------------------------------------------- zoom
    def press_zoom(self, e, vp, sp):
        self.drag = {"op": "zoomrect", "start": sp, "cur": sp, "vstart": QPointF(vp)}

    def move_zoom(self, e, vp, sp):
        if self.drag:
            self.drag["cur"] = sp

    def release_zoom(self, e, vp, sp):
        d, self.drag = self.drag, None
        if not d:
            return
        if abs(vp.x() - d["vstart"].x()) < 5 and abs(vp.y() - d["vstart"].y()) < 5:
            self.zoom_at(2.0, vp)
        else:
            self.zoom_to_rect(QRectF(d["start"], sp).normalized(), 0)

    # ------------------------------------------------------------ caneta
    def press_pen(self, e, vp, sp):
        if len(self.pen_nodes) >= 2:
            f = self.pen_nodes[0]
            if self.near(QPointF(f["x"], f["y"]), vp, 7):
                self.finish_pen(close=True)
                return
        self.pen_nodes.append(node(sp.x(), sp.y()))
        self.pen_dragging = True
        self.pen_press = QPointF(vp)

    def move_pen(self, e, vp, sp):
        if self.pen_dragging and self.pen_nodes:
            if abs(vp.x() - self.pen_press.x()) > 3 or abs(vp.y() - self.pen_press.y()) > 3:
                n = self.pen_nodes[-1]
                n["out"] = [sp.x(), sp.y()]
                n["in"] = [2 * n["x"] - sp.x(), 2 * n["y"] - sp.y()]
                n["smooth"] = True

    def release_pen(self, e, vp, sp):
        self.pen_dragging = False

    def finish_pen(self, close=False):
        nodes = self.pen_nodes
        self.pen_nodes = []
        self.pen_dragging = False
        self.viewport().update()
        if len(nodes) < 2:
            return
        if not close:
            nodes[0]["in"] = None
            nodes[-1]["out"] = None
        w = self.win
        s = Shape("path", paths=[{"nodes": nodes, "closed": close}],
                  fill=w.def_fill if close else None, stroke=w.def_stroke, stroke_w=w.def_stroke_w)
        w.add_shape(s)

    # --------------------------------------------------------- mão livre
    def press_free(self, e, vp, sp):
        self.free_pts = [(sp.x(), sp.y())]

    def move_free(self, e, vp, sp):
        if self.free_pts:
            lx, ly = self.free_pts[-1]
            if math.hypot(sp.x() - lx, sp.y() - ly) * self.scale_px() >= 2:
                self.free_pts.append((sp.x(), sp.y()))

    def release_free(self, e, vp, sp):
        pts, self.free_pts = self.free_pts, []
        if len(pts) < 2:
            return
        k = 1 / self.scale_px()
        pts = simplify(pts, 1.2 * k)
        closed = False
        if len(pts) > 3 and math.hypot(pts[0][0] - pts[-1][0], pts[0][1] - pts[-1][1]) < 8 * k:
            pts = pts[:-1]
            closed = True
        w = self.win
        s = Shape("path", paths=[{"nodes": smooth_nodes(pts, closed), "closed": closed}],
                  fill=w.def_fill if closed else None, stroke=w.def_stroke, stroke_w=w.def_stroke_w)
        w.add_shape(s)

    # ------------------------------------------------ retângulo/elipse/polígono
    def press_create(self, e, vp, sp):
        w = self.win
        kind = "path" if self.tool == "polygon" else self.tool
        s = Shape(kind, fill=w.def_fill, stroke=w.def_stroke, stroke_w=w.def_stroke_w, x=sp.x(), y=sp.y())
        self.drag = {"op": "create", "start": sp, "vstart": QPointF(vp), "shape": s,
                     "before": w.snapshot(), "tool": self.tool}
        w.shapes.append(s)
        w.add_item(s)
        w.set_selection([])

    def drag_rect(self, start, sp, mods):
        dx, dy = sp.x() - start.x(), sp.y() - start.y()
        if mods & Qt.KeyboardModifier.ControlModifier:
            m = max(abs(dx), abs(dy))
            dx, dy = math.copysign(m, dx or 1), math.copysign(m, dy or 1)
        if mods & Qt.KeyboardModifier.ShiftModifier:
            return QRectF(QPointF(start.x() - dx, start.y() - dy), QPointF(start.x() + dx, start.y() + dy)).normalized()
        return QRectF(start, QPointF(start.x() + dx, start.y() + dy)).normalized()

    def move_create(self, e, vp, sp):
        d = self.drag
        if not d or d.get("op") != "create":
            return
        r = self.drag_rect(d["start"], sp, e.modifiers())
        s = d["shape"]
        if d["tool"] == "polygon":
            s.paths = polygon_subpaths(r, self.win.poly_sides.value(), self.win.poly_star.isChecked())
        else:
            s.x, s.y, s.w, s.h = r.x(), r.y(), r.width(), r.height()
            if s.kind == "rect":
                s.radius = self.win.def_radius
        self.win.sync(s)
        self.win.refresh_props()

    def release_create(self, e, vp, sp):
        d, self.drag = self.drag, None
        if not d or d.get("op") != "create":
            return
        w = self.win
        s = d["shape"]
        tiny = abs(vp.x() - d["vstart"].x()) < 3 and abs(vp.y() - d["vstart"].y()) < 3
        if tiny or (s.kind == "path" and not s.paths):
            w.remove_item(s)
            w.shapes.remove(s)
            return
        w.set_selection([s])
        w.commit(d["before"])

    # ------------------------------------------------------------- texto
    def press_text(self, e, vp, sp):
        hit = self.hit_test(sp)
        if hit is not None and hit.kind == "text":
            self.win.edit_text(hit)
        else:
            self.win.create_text(sp)

    # ------------------------------------------------------------ teclado
    def keyPressEvent(self, e):
        k = e.key()
        mods = e.modifiers()
        w = self.win
        if k == Qt.Key.Key_Space:
            if not e.isAutoRepeat():
                self.space = True
                self.viewport().setCursor(Qt.CursorShape.OpenHandCursor)
            return
        if self.tool == "pen" and self.pen_nodes:
            if k in (Qt.Key.Key_Return, Qt.Key.Key_Enter, Qt.Key.Key_Escape):
                self.finish_pen()
                return
            if k == Qt.Key.Key_Backspace:
                self.pen_nodes.pop()
                self.viewport().update()
                return
        if k in (Qt.Key.Key_Delete, Qt.Key.Key_Backspace):
            w.delete_key()
            return
        if k == Qt.Key.Key_Escape:
            self.drag = None
            if self.tool == "shape" and self.node_sel is not None:
                self.node_sel = None
                self.viewport().update()
            else:
                w.set_selection([])
            return
        arrows = {Qt.Key.Key_Left: (-1, 0), Qt.Key.Key_Right: (1, 0),
                  Qt.Key.Key_Up: (0, -1), Qt.Key.Key_Down: (0, 1)}
        if k in arrows:
            step = 10.0 if mods & Qt.KeyboardModifier.ShiftModifier else (
                0.1 if mods & Qt.KeyboardModifier.ControlModifier else 1.0)
            dx, dy = arrows[k]
            w.nudge(dx * step, dy * step)
            return
        super().keyPressEvent(e)

    def keyReleaseEvent(self, e):
        if e.key() == Qt.Key.Key_Space and not e.isAutoRepeat():
            self.space = False
            self.apply_cursor()
            return
        super().keyReleaseEvent(e)

    def focusOutEvent(self, e):
        self.space = False
        super().focusOutEvent(e)


# ============================================================ janela principal
class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.shapes = []
        self.page_w, self.page_h = 210.0, 297.0
        self.selection = []
        self.undo_stack, self.redo_stack, self.clipboard = [], [], []
        self.path = None
        self.dirty = False
        self.def_fill = None
        self.def_stroke = "#000000"
        self.def_stroke_w = 0.2
        self.def_radius = 0.0
        self.scene = QGraphicsScene(self)
        self.canvas = Canvas(self)
        self._build_actions()
        self._build_menus()
        self._build_toolbars()
        self._build_central()
        self._build_docker()
        self._build_status()
        self.update_scene_rect()
        self.set_tool("pick")
        self.refresh_all()
        self.resize(1440, 880)
        QTimer.singleShot(0, self.canvas.zoom_page)

    # --------------------------------------------------------- construção
    def act(self, text, slot, shortcut=None, icon=None, tip=None):
        a = QAction(text, self)
        if icon:
            a.setIcon(make_icon(icon))
        if shortcut:
            a.setShortcut(QKeySequence(shortcut))
        if tip:
            a.setToolTip(tip)
        a.triggered.connect(slot)
        self.addAction(a)
        return a

    def _build_actions(self):
        A = self.act
        self.a_new = A("Novo", self.new_doc, "Ctrl+N", "new")
        self.a_open = A("Abrir...", self.open_doc, "Ctrl+O", "open")
        self.a_save = A("Salvar", self.save, "Ctrl+S", "save")
        self.a_save_as = A("Salvar como...", self.save_as, "Ctrl+Shift+S")
        self.a_export = A("Exportar (PDF, PNG, SVG)...", self.export, "Ctrl+E", "export")
        self.a_quit = A("Sair", self.close)
        self.a_undo = A("Desfazer", self.undo, "Ctrl+Z", "undo")
        self.a_redo = A("Refazer", self.redo, "Ctrl+Y", "redo")
        self.a_cut = A("Recortar", self.cut, "Ctrl+X")
        self.a_copy = A("Copiar", self.copy_sel, "Ctrl+C")
        self.a_paste = A("Colar", self.paste, "Ctrl+V")
        self.a_dup = A("Duplicar", self.duplicate, "Ctrl+D")
        self.a_selall = A("Selecionar tudo", self.select_all, "Ctrl+A")
        self.a_zin = A("Aproximar", lambda: self.canvas.zoom_at(1.5), "Ctrl++", "zoom_in")
        self.a_zout = A("Afastar", lambda: self.canvas.zoom_at(1 / 1.5), "Ctrl+-", "zoom_out")
        self.a_zpage = A("Zoom na página", self.canvas.zoom_page, "Shift+F4", "page")
        self.a_zobj = A("Zoom em todos os objetos", self.canvas.zoom_objects, "F4")
        self.a_zsel = A("Zoom na seleção", self.canvas.zoom_selection, "Shift+F2")
        self.a_z100 = A("Tamanho real (100%)", lambda: self.canvas.set_zoom_pct(100), "Ctrl+1")
        self.a_rulers = A("Réguas", self.toggle_rulers)
        self.a_rulers.setCheckable(True)
        self.a_rulers.setChecked(True)
        self.a_curves = A("Converter em curvas", self.to_curves, "Ctrl+Q")
        self.a_front = A("Para a frente", lambda: self.arrange("front"), "Shift+PgUp")
        self.a_back = A("Para trás", lambda: self.arrange("back"), "Shift+PgDown")
        self.a_fwd = A("Avançar um", lambda: self.arrange("forward"), "Ctrl+PgUp")
        self.a_bwd = A("Recuar um", lambda: self.arrange("backward"), "Ctrl+PgDown")
        self.a_al = A("Alinhar à esquerda", lambda: self.align("left"), "L")
        self.a_ar = A("Alinhar à direita", lambda: self.align("right"), "R")
        self.a_at = A("Alinhar ao topo", lambda: self.align("top"), "T")
        self.a_ab = A("Alinhar à base", lambda: self.align("bottom"), "B")
        self.a_ac = A("Alinhar centros na vertical", lambda: self.align("vcenter"), "C")
        self.a_ae = A("Alinhar centros na horizontal", lambda: self.align("hcenter"), "E")
        self.a_mh = A("Espelhar na horizontal", lambda: self.mirror(True))
        self.a_mv = A("Espelhar na vertical", lambda: self.mirror(False))
        self.a_rl = A("Girar 90° anti-horário", lambda: self.rotate_selection(90))
        self.a_rr = A("Girar 90° horário", lambda: self.rotate_selection(-90))
        self.a_help = A("Atalhos e dicas", self.show_help, "F1")
        self.a_about = A("Sobre", lambda: QMessageBox.about(
            self, APP, f"<b>{APP} 2</b><br>Editor de desenho vetorial feito em Python + Qt."))
        self.tool_group = QActionGroup(self)
        self.tool_acts = {}
        for key, name, sc in TOOLS:
            a = QAction(make_icon(key), name, self)
            a.setCheckable(True)
            a.setShortcut(QKeySequence(sc))
            a.setToolTip(f"{name} ({sc})")
            a.triggered.connect(lambda checked=False, k=key: self.set_tool(k))
            self.tool_group.addAction(a)
            self.addAction(a)
            self.tool_acts[key] = a

    def _build_menus(self):
        mb = self.menuBar()
        m = mb.addMenu("&Arquivo")
        for a in (self.a_new, self.a_open, None, self.a_save, self.a_save_as, None, self.a_export, None, self.a_quit):
            m.addSeparator() if a is None else m.addAction(a)
        m = mb.addMenu("&Editar")
        for a in (self.a_undo, self.a_redo, None, self.a_cut, self.a_copy, self.a_paste, self.a_dup, None, self.a_selall):
            m.addSeparator() if a is None else m.addAction(a)
        m.addAction("Excluir", self.delete_key, QKeySequence("Del"))
        m = mb.addMenu("E&xibir")
        for a in (self.a_zin, self.a_zout, None, self.a_zpage, self.a_zobj, self.a_zsel, self.a_z100, None, self.a_rulers):
            m.addSeparator() if a is None else m.addAction(a)
        m = mb.addMenu("&Layout")
        m.addAction("Tamanho da página...", self.ask_page_size)
        m = mb.addMenu("&Objeto")
        m.addAction(self.a_curves)
        sm = m.addMenu("Organizar")
        for a in (self.a_front, self.a_back, self.a_fwd, self.a_bwd):
            sm.addAction(a)
        sm = m.addMenu("Alinhar")
        for a in (self.a_al, self.a_ar, self.a_at, self.a_ab, self.a_ac, self.a_ae):
            sm.addAction(a)
        sm = m.addMenu("Transformar")
        for a in (self.a_rl, self.a_rr, self.a_mh, self.a_mv):
            sm.addAction(a)
        m = mb.addMenu("&Ferramentas")
        for key, _, _ in TOOLS:
            m.addAction(self.tool_acts[key])
        m = mb.addMenu("A&juda")
        m.addAction(self.a_help)
        m.addAction(self.a_about)

    def _spin(self, lo, hi, dec=2, suffix=" mm", step=1.0, slot=None, width=92):
        s = QDoubleSpinBox()
        s.setRange(lo, hi)
        s.setDecimals(dec)
        s.setSuffix(suffix)
        s.setSingleStep(step)
        s.setKeyboardTracking(False)
        s.setFixedWidth(width)
        if slot:
            s.valueChanged.connect(slot)
        return s

    def _build_toolbars(self):
        tb = QToolBar("Barra padrão")
        tb.setObjectName("std")
        tb.setMovable(False)
        tb.setIconSize(QSize(20, 20))
        for a in (self.a_new, self.a_open, self.a_save, self.a_export, None, self.a_undo, self.a_redo, None):
            tb.addSeparator() if a is None else tb.addAction(a)
        self.zoom_combo = QComboBox()
        self.zoom_combo.setEditable(True)
        self.zoom_combo.addItems(["Página", "Objetos", "25%", "50%", "75%", "100%", "200%", "400%", "800%", "1600%"])
        self.zoom_combo.setFixedWidth(100)
        self.zoom_combo.activated.connect(lambda i: self.on_zoom_text(self.zoom_combo.itemText(i)))
        self.zoom_combo.lineEdit().returnPressed.connect(lambda: self.on_zoom_text(self.zoom_combo.currentText()))
        tb.addWidget(self.zoom_combo)
        for a in (self.a_zin, self.a_zout, self.a_zpage):
            tb.addAction(a)
        self.addToolBar(Qt.ToolBarArea.TopToolBarArea, tb)
        self.addToolBarBreak()

        pb = QToolBar("Barra de propriedades")
        pb.setObjectName("props")
        pb.setMovable(False)
        self.prop_bar = pb

        def lab(t):
            return QLabel(t)

        add = pb.addWidget
        # página
        self.page_combo = QComboBox()
        self.page_combo.addItems(list(PAGES) + ["Personalizado"])
        self.page_combo.activated.connect(self.on_page_preset)
        self.page_w_spin = self._spin(10, 5000, slot=lambda v: self.on_page_custom())
        self.page_h_spin = self._spin(10, 5000, slot=lambda v: self.on_page_custom())
        b_port = QToolButton()
        b_port.setText("Retrato")
        b_port.clicked.connect(lambda: self.set_orientation(False))
        b_land = QToolButton()
        b_land.setText("Paisagem")
        b_land.clicked.connect(lambda: self.set_orientation(True))
        self.page_acts = [add(lab("  Página ")), add(self.page_combo), add(lab("  L ")), add(self.page_w_spin),
                          add(lab("  A ")), add(self.page_h_spin), add(b_port), add(b_land)]
        # objeto
        self.x_spin = self._spin(-10000, 10000, slot=lambda v: self.on_geom("x"))
        self.y_spin = self._spin(-10000, 10000, slot=lambda v: self.on_geom("y"))
        self.w_spin = self._spin(0.01, 20000, slot=lambda v: self.on_geom("w"))
        self.h_spin = self._spin(0.01, 20000, slot=lambda v: self.on_geom("h"))
        self.lock_ratio = QToolButton()
        self.lock_ratio.setText("🔒")
        self.lock_ratio.setCheckable(True)
        self.lock_ratio.setToolTip("Manter proporção ao digitar largura/altura")
        self.angle_spin = self._spin(-360, 360, dec=1, suffix=" °", step=5, slot=lambda v: self.on_angle(), width=78)
        b_mh = QToolButton()
        b_mh.setText("⇆")
        b_mh.setToolTip("Espelhar na horizontal")
        b_mh.clicked.connect(lambda: self.mirror(True))
        b_mv = QToolButton()
        b_mv.setText("⇅")
        b_mv.setToolTip("Espelhar na vertical")
        b_mv.clicked.connect(lambda: self.mirror(False))
        self.obj_acts = [add(lab("  X ")), add(self.x_spin), add(lab(" Y ")), add(self.y_spin),
                         add(lab("  L ")), add(self.w_spin), add(lab(" A ")), add(self.h_spin),
                         add(self.lock_ratio), add(lab("  ⟲ ")), add(self.angle_spin), add(b_mh), add(b_mv)]
        # retângulo
        self.radius_spin = self._spin(0, 5000, slot=lambda v: self.on_radius())
        self.rect_acts = [add(lab("  Cantos ")), add(self.radius_spin)]
        # texto
        self.font_combo = QFontComboBox()
        self.font_combo.setCurrentFont(QFont("Arial"))
        self.font_combo.setFixedWidth(170)
        self.font_combo.currentFontChanged.connect(lambda f: self.on_font())
        self.size_spin = self._spin(1, 2000, dec=1, suffix=" pt", step=1, slot=lambda v: self.on_font(), width=80)
        self.size_spin.setValue(24)
        self.text_acts = [add(lab("  Fonte ")), add(self.font_combo), add(self.size_spin)]
        # polígono
        self.poly_sides = QSpinBox()
        self.poly_sides.setRange(3, 60)
        self.poly_sides.setValue(5)
        self.poly_star = QCheckBox("Estrela")
        self.poly_acts = [add(lab("  Lados ")), add(self.poly_sides), add(self.poly_star)]
        # nós
        self.node_acts = [add(lab("  Nó: "))]
        for text, tip, fn in (("Suave", "Tornar o nó suave", self.node_smooth),
                              ("Cúspide", "Tornar o nó um canto (alças independentes)", self.node_cusp),
                              ("→ Linha", "Converter o segmento seguinte em reta", self.seg_to_line),
                              ("→ Curva", "Converter o segmento seguinte em curva", self.seg_to_curve),
                              ("Fechar/Abrir", "Fechar ou abrir a curva", self.toggle_closed),
                              ("Excluir nó", "Excluir o nó selecionado (Del)", self.delete_node)):
            b = QToolButton()
            b.setText(text)
            b.setToolTip(tip)
            b.clicked.connect(fn)
            self.node_acts.append(add(b))
        # contorno (sempre visível)
        pb.addSeparator()
        self.sw_spin = self._spin(0, 100, dec=3, suffix=" mm", step=0.1, slot=lambda v: self.on_stroke_w(v), width=96)
        add(lab("  Contorno "))
        add(self.sw_spin)
        self.hint = QLabel()
        self.hint.setStyleSheet("color:#9ab; padding-left:12px;")
        add(self.hint)
        self.addToolBar(Qt.ToolBarArea.TopToolBarArea, pb)

        box = QToolBar("Caixa de ferramentas")
        box.setObjectName("tools")
        box.setMovable(False)
        box.setIconSize(QSize(26, 26))
        for key, _, _ in TOOLS:
            box.addAction(self.tool_acts[key])
            if key in ("shape", "pan", "pen", "polygon"):
                box.addSeparator()
        self.addToolBar(Qt.ToolBarArea.LeftToolBarArea, box)

        palbar = QToolBar("Paleta de cores")
        palbar.setObjectName("palette")
        palbar.setMovable(False)
        self.palette_bar = PaletteBar()
        self.palette_bar.colorClicked.connect(self.on_palette)
        palbar.addWidget(self.palette_bar)
        self.addToolBar(Qt.ToolBarArea.RightToolBarArea, palbar)

    def _build_central(self):
        w = QWidget()
        g = QGridLayout(w)
        g.setContentsMargins(0, 0, 0, 0)
        g.setSpacing(0)
        self.corner = QLabel()
        self.corner.setFixedSize(RULER, RULER)
        self.corner.setStyleSheet("background:#262626;")
        self.hruler = Ruler(self.canvas, True)
        self.vruler = Ruler(self.canvas, False)
        g.addWidget(self.corner, 0, 0)
        g.addWidget(self.hruler, 0, 1)
        g.addWidget(self.vruler, 1, 0)
        g.addWidget(self.canvas, 1, 1)
        self.setCentralWidget(w)
        upd = self.update_rulers
        self.canvas.horizontalScrollBar().valueChanged.connect(upd)
        self.canvas.verticalScrollBar().valueChanged.connect(upd)
        self.canvas.zoomChanged.connect(self.on_zoom_changed)
        self.canvas.mouseMoved.connect(self.on_mouse_moved)

    def _build_docker(self):
        dock = QDockWidget("Propriedades", self)
        dock.setObjectName("dock")
        dock.setFeatures(QDockWidget.DockWidgetFeature.DockWidgetMovable)
        tabs = QTabWidget()
        props = QWidget()
        v = QVBoxLayout(props)

        g1 = QGroupBox("Preenchimento")
        h1 = QHBoxLayout(g1)
        self.fill_btn = QPushButton()
        self.fill_btn.setFixedSize(46, 24)
        self.fill_btn.clicked.connect(self.pick_fill)
        b = QPushButton("Nenhum")
        b.clicked.connect(lambda: self.set_fill(None))
        h1.addWidget(self.fill_btn)
        h1.addWidget(b)
        h1.addStretch()

        g2 = QGroupBox("Contorno")
        gl = QGridLayout(g2)
        self.stroke_btn = QPushButton()
        self.stroke_btn.setFixedSize(46, 24)
        self.stroke_btn.clicked.connect(self.pick_stroke)
        b2 = QPushButton("Nenhum")
        b2.clicked.connect(lambda: self.set_stroke(None))
        self.sw_spin2 = self._spin(0, 100, dec=3, step=0.1, slot=lambda val: self.on_stroke_w(val), width=100)
        gl.addWidget(self.stroke_btn, 0, 0)
        gl.addWidget(b2, 0, 1)
        gl.addWidget(QLabel("Largura"), 1, 0)
        gl.addWidget(self.sw_spin2, 1, 1)

        def button_grid(title, items, cols=2):
            g = QGroupBox(title)
            lay = QGridLayout(g)
            for i, (text, fn) in enumerate(items):
                bt = QPushButton(text)
                bt.clicked.connect(fn)
                lay.addWidget(bt, i // cols, i % cols)
            return g

        g3 = button_grid("Transformar", [("Girar 90° ↺", lambda: self.rotate_selection(90)),
                                          ("Girar 90° ↻", lambda: self.rotate_selection(-90)),
                                          ("Espelhar ⇆", lambda: self.mirror(True)),
                                          ("Espelhar ⇅", lambda: self.mirror(False)),
                                          ("Converter em curvas", self.to_curves)])
        g4 = button_grid("Organizar", [("Para a frente", lambda: self.arrange("front")),
                                        ("Para trás", lambda: self.arrange("back")),
                                        ("Avançar um", lambda: self.arrange("forward")),
                                        ("Recuar um", lambda: self.arrange("backward"))])
        g5 = button_grid("Alinhar (seleção ou página)", [
            ("Esquerda", lambda: self.align("left")), ("Direita", lambda: self.align("right")),
            ("Topo", lambda: self.align("top")), ("Base", lambda: self.align("bottom")),
            ("Centro vertical", lambda: self.align("vcenter")),
            ("Centro horizontal", lambda: self.align("hcenter"))])
        for g in (g1, g2, g3, g4, g5):
            v.addWidget(g)
        v.addStretch()
        tabs.addTab(props, "Propriedades")

        self.obj_list = QListWidget()
        self.obj_list.setSelectionMode(QAbstractItemView.SelectionMode.ExtendedSelection)
        self.obj_list.itemSelectionChanged.connect(self.on_list_select)
        objs = QWidget()
        ov = QVBoxLayout(objs)
        ov.addWidget(QLabel("Camada 1  (o topo da lista fica na frente)"))
        ov.addWidget(self.obj_list)
        tabs.addTab(objs, "Objetos")
        dock.setWidget(tabs)
        dock.setMinimumWidth(250)
        self.addDockWidget(Qt.DockWidgetArea.RightDockWidgetArea, dock)

    def _build_status(self):
        sb = self.statusBar()
        self.coord_label = QLabel()
        self.coord_label.setMinimumWidth(190)
        self.info_label = QLabel()
        sb.addWidget(self.coord_label)
        sb.addWidget(self.info_label, 1)
        self.fill_sw = QLabel()
        self.fill_sw.setFixedSize(16, 16)
        self.fill_txt = QLabel()
        self.stroke_sw = QLabel()
        self.stroke_sw.setFixedSize(16, 16)
        self.stroke_txt = QLabel()
        for wdg in (QLabel("Preench."), self.fill_sw, self.fill_txt, QLabel("   Contorno"), self.stroke_sw, self.stroke_txt):
            sb.addPermanentWidget(wdg)

    # ---------------------------------------------------- documento/estado
    def snapshot(self):
        return {"page": [self.page_w, self.page_h], "shapes": [s.to_dict() for s in self.shapes]}

    def restore(self, snap):
        self.page_w, self.page_h = snap["page"]
        self.shapes = [Shape.from_dict(d) for d in snap["shapes"]]
        self.selection = []
        self.canvas.edit = None
        self.canvas.node_sel = None
        self.rebuild()

    def rebuild(self):
        self.scene.clear()
        for s in self.shapes:
            s.item = None
            self.add_item(s)
        self.restack()
        self.update_scene_rect()
        self.refresh_all()

    def add_item(self, s):
        item = ShapeItem(s)
        item.setZValue(len(self.shapes))
        self.scene.addItem(item)

    def remove_item(self, s):
        if s.item is not None:
            self.scene.removeItem(s.item)
            s.item = None

    def restack(self):
        for i, s in enumerate(self.shapes):
            if s.item:
                s.item.setZValue(i)

    def sync(self, s):
        if s.item is not None:
            s.item.sync()

    def commit(self, before):
        if before == self.snapshot():
            self.refresh_all()
            return False
        self.undo_stack.append(before)
        if len(self.undo_stack) > MAX_UNDO:
            self.undo_stack.pop(0)
        self.redo_stack.clear()
        self.set_dirty(True)
        self.refresh_all()
        return True

    def undo(self):
        if self.canvas.pen_nodes:
            self.canvas.pen_nodes = []
            self.canvas.viewport().update()
            return
        if not self.undo_stack:
            return
        self.redo_stack.append(self.snapshot())
        self.restore(self.undo_stack.pop())
        self.set_dirty(True)

    def redo(self):
        if not self.redo_stack:
            return
        self.undo_stack.append(self.snapshot())
        self.restore(self.redo_stack.pop())
        self.set_dirty(True)

    def set_dirty(self, v):
        self.dirty = v
        name = self.path.replace("\\", "/").split("/")[-1] if self.path else "Sem título"
        self.setWindowTitle(f"{APP} - {'*' if v else ''}{name}")

    def update_scene_rect(self):
        self.scene.setSceneRect(-DESK, -DESK, self.page_w + 2 * DESK, self.page_h + 2 * DESK)
        self.canvas.viewport().update()
        self.update_rulers()

    def add_shape(self, s, before=None):
        before = before or self.snapshot()
        self.shapes.append(s)
        self.add_item(s)
        self.set_selection([s])
        self.commit(before)

    def selection_bounds(self):
        r = QRectF()
        for i, s in enumerate(self.selection):
            b = s.scene_bounds()
            r = b if i == 0 else r.united(b)
        return r

    def set_selection(self, sel, from_list=False):
        sel = [s for s in sel if s in self.shapes]
        if sel != self.selection:
            self.canvas.rotate_mode = False
        self.selection = sel
        if self.canvas.tool == "shape":
            new_edit = sel[0] if len(sel) == 1 else None
            if new_edit is not self.canvas.edit:
                self.canvas.node_sel = None
            self.canvas.edit = new_edit
        if not from_list:
            self.sync_list_selection()
        self.refresh_props()
        self.canvas.viewport().update()

    # ------------------------------------------------------ atualizações
    def refresh_all(self):
        self.refresh_objects()
        self.refresh_props()
        self.canvas.viewport().update()
        self.update_rulers()

    def update_rulers(self, *args):
        self.hruler.update()
        self.vruler.update()

    def on_zoom_changed(self, pct):
        self.zoom_combo.setEditText(f"{pct:.0f}%")
        self.update_rulers()

    def on_mouse_moved(self, sp):
        self.coord_label.setText(f"X: {fmt(sp.x(), 3)} mm   Y: {fmt(sp.y(), 3)} mm")
        self.update_rulers()

    def on_zoom_text(self, text):
        t = text.strip().replace("%", "").replace(",", ".")
        if text.startswith("Página"):
            self.canvas.zoom_page()
        elif text.startswith("Objetos"):
            self.canvas.zoom_objects()
        else:
            try:
                self.canvas.set_zoom_pct(float(t))
            except ValueError:
                pass
        self.canvas.setFocus()

    def refresh_objects(self):
        lw = self.obj_list
        lw.blockSignals(True)
        lw.clear()
        for s in reversed(self.shapes):
            it = QListWidgetItem(s.describe())
            it.setData(Qt.ItemDataRole.UserRole, id(s))
            lw.addItem(it)
            it.setSelected(s in self.selection)
        lw.blockSignals(False)

    def sync_list_selection(self):
        lw = self.obj_list
        lw.blockSignals(True)
        ids = {id(s) for s in self.selection}
        for i in range(lw.count()):
            it = lw.item(i)
            it.setSelected(it.data(Qt.ItemDataRole.UserRole) in ids)
        lw.blockSignals(False)

    def on_list_select(self):
        ids = {it.data(Qt.ItemDataRole.UserRole) for it in self.obj_list.selectedItems()}
        self.set_selection([s for s in self.shapes if id(s) in ids], from_list=True)

    def refresh_props(self):
        sel = self.selection
        tool = self.canvas.tool
        for a in self.page_acts:
            a.setVisible(not sel and tool in ("pick", "zoom", "pan"))
        for a in self.obj_acts:
            a.setVisible(bool(sel))
        rects = [s for s in sel if s.kind == "rect"]
        texts = [s for s in sel if s.kind == "text"]
        for a in self.rect_acts:
            a.setVisible(bool(rects) or tool == "rect")
        for a in self.text_acts:
            a.setVisible(bool(texts) or tool == "text")
        for a in self.poly_acts:
            a.setVisible(tool == "polygon")
        for a in self.node_acts:
            a.setVisible(tool == "shape")
        self.hint.setText(HINTS.get(tool, ""))
        widgets = (self.page_combo, self.page_w_spin, self.page_h_spin, self.x_spin, self.y_spin,
                   self.w_spin, self.h_spin, self.angle_spin, self.sw_spin, self.sw_spin2,
                   self.radius_spin, self.font_combo, self.size_spin)
        for wdg in widgets:
            wdg.blockSignals(True)
        try:
            preset = next((k for k, (pw, ph) in PAGES.items()
                           if {round(pw, 1), round(ph, 1)} == {round(self.page_w, 1), round(self.page_h, 1)}),
                          "Personalizado")
            self.page_combo.setCurrentText(preset)
            self.page_w_spin.setValue(self.page_w)
            self.page_h_spin.setValue(self.page_h)
            if sel:
                r = self.selection_bounds()
                self.x_spin.setValue(r.x())
                self.y_spin.setValue(r.y())
                self.w_spin.setValue(max(r.width(), 0.01))
                self.h_spin.setValue(max(r.height(), 0.01))
                ang = ((-sel[0].angle + 180) % 360) - 180 if len(sel) == 1 else 0.0
                self.angle_spin.setValue(round(ang, 1) + 0.0)
                ref = sel[0]
                sw = ref.stroke_w if ref.stroke else 0.0
            else:
                sw = self.def_stroke_w if self.def_stroke else 0.0
            self.sw_spin.setValue(sw)
            self.sw_spin2.setValue(sw)
            self.radius_spin.setValue(rects[0].radius if rects else self.def_radius)
            if texts:
                self.font_combo.setCurrentFont(QFont(texts[0].font))
                self.size_spin.setValue(texts[0].size)
        finally:
            for wdg in widgets:
                wdg.blockSignals(False)
        self.refresh_status()

    def refresh_status(self):
        sel = self.selection
        if not sel:
            info = "Nenhum objeto selecionado  (cores clicadas agora valem para novos objetos)"
            fill, stroke, sw = self.def_fill, self.def_stroke, self.def_stroke_w
        else:
            info = f"{sel[0].describe()} na Camada 1" if len(sel) == 1 else f"{len(sel)} objetos selecionados na Camada 1"
            fill, stroke, sw = sel[0].fill, sel[0].stroke, sel[0].stroke_w
        if self.canvas.tool == "shape" and self.canvas.node_sel is not None:
            info += "  •  1 nó selecionado"
        self.info_label.setText(info)

        def paint_sw(lbl, c):
            if c:
                lbl.setStyleSheet(f"background:{c}; border:1px solid #888;")
                lbl.setText("")
            else:
                lbl.setStyleSheet("background:white; color:#e30613; border:1px solid #888;")
                lbl.setText("✕")
                lbl.setAlignment(Qt.AlignmentFlag.AlignCenter)

        paint_sw(self.fill_sw, fill)
        paint_sw(self.stroke_sw, stroke)
        self.fill_txt.setText(fill.upper() if fill else "Nenhum")
        self.stroke_txt.setText(f"{stroke.upper()}  {fmt(sw, 3)} mm" if stroke else "Nenhum")
        for btn, c in ((self.fill_btn, fill), (self.stroke_btn, stroke)):
            btn.setStyleSheet(f"background:{c}; border:1px solid #888;" if c else
                              "background:white; color:#e30613; border:1px solid #888;")
            btn.setText("" if c else "✕")

    # -------------------------------------------------------- ferramentas
    def set_tool(self, key):
        c = self.canvas
        if c.tool == "pen" and key != "pen":
            c.finish_pen()
        c.drag = None
        c.free_pts = []
        c.tool = key
        c.rotate_mode = False
        if key == "shape":
            c.edit = self.selection[0] if len(self.selection) == 1 else None
            c.node_sel = None
        self.tool_acts[key].setChecked(True)
        c.apply_cursor()
        self.refresh_props()
        c.viewport().update()
        c.setFocus()

    # ---------------------------------------------------------- edição
    def on_palette(self, color, is_stroke):
        if is_stroke:
            self.set_stroke(color)
        else:
            self.set_fill(color)

    def set_fill(self, color):
        if not self.selection:
            self.def_fill = color
            self.refresh_status()
            return
        before = self.snapshot()
        for s in self.selection:
            s.fill = color
            self.sync(s)
        self.commit(before)

    def set_stroke(self, color):
        if not self.selection:
            self.def_stroke = color
            self.refresh_props()
            return
        before = self.snapshot()
        for s in self.selection:
            s.stroke = color
            if color and s.stroke_w <= 0:
                s.stroke_w = 0.2
            self.sync(s)
        self.commit(before)

    def pick_fill(self):
        ref = self.selection[0].fill if self.selection else self.def_fill
        c = QColorDialog.getColor(QColor(ref or "#ffffff"), self, "Cor do preenchimento")
        if c.isValid():
            self.set_fill(c.name())

    def pick_stroke(self):
        ref = self.selection[0].stroke if self.selection else self.def_stroke
        c = QColorDialog.getColor(QColor(ref or "#000000"), self, "Cor do contorno")
        if c.isValid():
            self.set_stroke(c.name())

    def on_stroke_w(self, v):
        if not self.selection:
            self.def_stroke_w = v
            if v > 0 and not self.def_stroke:
                self.def_stroke = "#000000"
            self.refresh_props()
            return
        before = self.snapshot()
        for s in self.selection:
            s.stroke_w = v
            if v > 0 and not s.stroke:
                s.stroke = "#000000"
            self.sync(s)
        self.commit(before)

    def on_radius(self):
        v = self.radius_spin.value()
        rects = [s for s in self.selection if s.kind == "rect"]
        if not rects:
            self.def_radius = v
            return
        before = self.snapshot()
        for s in rects:
            s.radius = v
            self.sync(s)
        self.commit(before)

    def on_font(self):
        family = self.font_combo.currentFont().family()
        size = self.size_spin.value()
        texts = [s for s in self.selection if s.kind == "text"]
        if not texts:
            return
        before = self.snapshot()
        for s in texts:
            s.font, s.size = family, size
            self.sync(s)
        self.commit(before)

    def transform_selection(self, M):
        if not self.selection:
            return
        before = self.snapshot()
        for s in self.selection:
            s.apply(M)
            self.sync(s)
        self.commit(before)

    def on_geom(self, field):
        if not self.selection:
            return
        r = self.selection_bounds()
        tl = r.topLeft()
        if field == "x":
            M = QTransform.fromTranslate(self.x_spin.value() - r.x(), 0)
        elif field == "y":
            M = QTransform.fromTranslate(0, self.y_spin.value() - r.y())
        elif field == "w":
            if r.width() < 1e-6:
                return
            sx = self.w_spin.value() / r.width()
            M = T_about(QTransform.fromScale(sx, sx if self.lock_ratio.isChecked() else 1), tl)
        else:
            if r.height() < 1e-6:
                return
            sy = self.h_spin.value() / r.height()
            M = T_about(QTransform.fromScale(sy if self.lock_ratio.isChecked() else 1, sy), tl)
        self.transform_selection(M)

    def on_angle(self):
        if not self.selection:
            return
        v = self.angle_spin.value()
        cur = ((-self.selection[0].angle + 180) % 360) - 180 if len(self.selection) == 1 else 0.0
        self.rotate_selection(v - cur)

    def rotate_selection(self, deg_ccw):
        if self.selection:
            self.transform_selection(T_about(QTransform().rotate(-deg_ccw), self.selection_bounds().center()))

    def mirror(self, horizontal):
        if self.selection:
            m = QTransform.fromScale(-1, 1) if horizontal else QTransform.fromScale(1, -1)
            self.transform_selection(T_about(m, self.selection_bounds().center()))

    def nudge(self, dx, dy):
        c = self.canvas
        if c.tool == "shape" and c.edit is not None and c.node_sel is not None and c.edit.kind == "path":
            s = c.edit
            before = self.snapshot()
            inv = s.transform().inverted()[0]
            o, d = inv.map(QPointF(0, 0)), inv.map(QPointF(dx, dy))
            lx, ly = d.x() - o.x(), d.y() - o.y()
            n = s.paths[c.node_sel[0]]["nodes"][c.node_sel[1]]
            n["x"] += lx
            n["y"] += ly
            for k in ("in", "out"):
                if n[k] is not None:
                    n[k] = [n[k][0] + lx, n[k][1] + ly]
            self.sync(s)
            self.commit(before)
            return
        self.transform_selection(QTransform.fromTranslate(dx, dy))

    def align(self, mode):
        sel = self.selection
        if not sel:
            return
        ref = self.selection_bounds() if len(sel) > 1 else QRectF(0, 0, self.page_w, self.page_h)
        before = self.snapshot()
        for s in sel:
            b = s.scene_bounds()
            dx = dy = 0.0
            if mode == "left":
                dx = ref.left() - b.left()
            elif mode == "right":
                dx = ref.right() - b.right()
            elif mode == "top":
                dy = ref.top() - b.top()
            elif mode == "bottom":
                dy = ref.bottom() - b.bottom()
            elif mode == "vcenter":
                dx = ref.center().x() - b.center().x()
            elif mode == "hcenter":
                dy = ref.center().y() - b.center().y()
            s.apply(QTransform.fromTranslate(dx, dy))
            self.sync(s)
        self.commit(before)

    def arrange(self, mode):
        sel = [s for s in self.shapes if s in self.selection]
        if not sel:
            return
        before = self.snapshot()
        sh = self.shapes
        if mode == "front":
            self.shapes = [s for s in sh if s not in sel] + sel
        elif mode == "back":
            self.shapes = sel + [s for s in sh if s not in sel]
        elif mode == "forward":
            for i in range(len(sh) - 2, -1, -1):
                if sh[i] in sel and sh[i + 1] not in sel:
                    sh[i], sh[i + 1] = sh[i + 1], sh[i]
        elif mode == "backward":
            for i in range(1, len(sh)):
                if sh[i] in sel and sh[i - 1] not in sel:
                    sh[i], sh[i - 1] = sh[i - 1], sh[i]
        self.restack()
        self.commit(before)

    def to_curves(self):
        targets = [s for s in self.selection if s.kind != "path"]
        if not targets:
            return
        before = self.snapshot()
        for s in targets:
            s.to_curves()
            self.sync(s)
        self.commit(before)
        if self.canvas.tool == "shape":
            self.canvas.edit = self.selection[0] if len(self.selection) == 1 else None
            self.canvas.viewport().update()

    def delete_key(self):
        """Del: na ferramenta Forma exclui o nó; nas outras, os objetos."""
        c = self.canvas
        if c.tool == "shape" and c.node_sel is not None:
            self.delete_node()
        else:
            self.delete_selection()

    def delete_selection(self):
        if not self.selection:
            return
        before = self.snapshot()
        for s in self.selection:
            self.remove_item(s)
            self.shapes.remove(s)
        self.selection = []
        self.canvas.edit = None
        self.canvas.node_sel = None
        self.restack()
        self.commit(before)

    def copy_sel(self):
        self.clipboard = [s.to_dict() for s in self.shapes if s in self.selection]

    def cut(self):
        self.copy_sel()
        self.delete_selection()

    def paste(self, offset=0.0):
        if not self.clipboard:
            return
        before = self.snapshot()
        new = []
        for d in self.clipboard:
            s = Shape.from_dict(d)
            if offset:
                s.apply(QTransform.fromTranslate(offset, offset))
            self.shapes.append(s)
            self.add_item(s)
            new.append(s)
        self.set_selection(new)
        self.commit(before)

    def duplicate(self):
        if not self.selection:
            return
        saved = self.clipboard
        self.copy_sel()
        self.paste(5.0)
        self.clipboard = saved

    def select_all(self):
        if self.canvas.tool not in ("pick", "shape"):
            self.set_tool("pick")
        self.set_selection(list(self.shapes))

    # --------------------------------------------------------------- nós
    def _edit_node(self):
        c = self.canvas
        s = c.edit
        if s is None or s.kind != "path" or c.node_sel is None:
            return None, None, None
        si, ni = c.node_sel
        if si >= len(s.paths) or ni >= len(s.paths[si]["nodes"]):
            return None, None, None
        return s, s.paths[si], ni

    def node_smooth(self):
        s, sub, ni = self._edit_node()
        if s is None:
            return
        before = self.snapshot()
        nodes, n = sub["nodes"], len(sub["nodes"])
        cur = nodes[ni]
        prev = nodes[(ni - 1) % n] if (ni > 0 or sub["closed"]) else None
        nxt = nodes[(ni + 1) % n] if (ni < n - 1 or sub["closed"]) else None
        a = (prev["x"], prev["y"]) if prev else (cur["x"], cur["y"])
        b = (nxt["x"], nxt["y"]) if nxt else (cur["x"], cur["y"])
        dx, dy = b[0] - a[0], b[1] - a[1]
        L = math.hypot(dx, dy) or 1.0
        ux, uy = dx / L, dy / L

        def length(key, other):
            if cur[key] is not None:
                return math.hypot(cur[key][0] - cur["x"], cur[key][1] - cur["y"])
            return math.hypot(other[0] - cur["x"], other[1] - cur["y"]) / 3

        if prev:
            li = length("in", a)
            cur["in"] = [cur["x"] - ux * li, cur["y"] - uy * li]
        if nxt:
            lo = length("out", b)
            cur["out"] = [cur["x"] + ux * lo, cur["y"] + uy * lo]
        cur["smooth"] = True
        self.sync(s)
        self.commit(before)

    def node_cusp(self):
        s, sub, ni = self._edit_node()
        if s is None:
            return
        before = self.snapshot()
        sub["nodes"][ni]["smooth"] = False
        self.commit(before)

    def seg_to_line(self):
        s, sub, ni = self._edit_node()
        if s is None:
            return
        nodes, n = sub["nodes"], len(sub["nodes"])
        if ni == n - 1 and not sub["closed"]:
            return
        before = self.snapshot()
        nodes[ni]["out"] = None
        nodes[(ni + 1) % n]["in"] = None
        nodes[ni]["smooth"] = nodes[(ni + 1) % n]["smooth"] = False
        self.sync(s)
        self.commit(before)

    def seg_to_curve(self):
        s, sub, ni = self._edit_node()
        if s is None:
            return
        nodes, n = sub["nodes"], len(sub["nodes"])
        if ni == n - 1 and not sub["closed"]:
            return
        a, b = nodes[ni], nodes[(ni + 1) % n]
        if a["out"] is not None or b["in"] is not None:
            return
        before = self.snapshot()
        dx, dy = b["x"] - a["x"], b["y"] - a["y"]
        a["out"] = [a["x"] + dx / 3, a["y"] + dy / 3]
        b["in"] = [a["x"] + 2 * dx / 3, a["y"] + 2 * dy / 3]
        self.sync(s)
        self.commit(before)

    def toggle_closed(self):
        c = self.canvas
        s = c.edit
        if s is None or s.kind != "path" or not s.paths:
            return
        si = c.node_sel[0] if c.node_sel else 0
        before = self.snapshot()
        s.paths[si]["closed"] = not s.paths[si]["closed"]
        self.sync(s)
        self.commit(before)

    def delete_node(self):
        s, sub, ni = self._edit_node()
        if s is None:
            return
        before = self.snapshot()
        c = self.canvas
        if len(sub["nodes"]) > 2:
            sub["nodes"].pop(ni)
            c.node_sel = (c.node_sel[0], max(0, ni - 1))
        else:
            s.paths.remove(sub)
            c.node_sel = None
        if not s.paths:
            self.remove_item(s)
            self.shapes.remove(s)
            self.selection = []
            c.edit = None
            self.restack()
        else:
            self.sync(s)
        self.commit(before)

    # ------------------------------------------------------------- texto
    def create_text(self, sp):
        txt, ok = QInputDialog.getMultiLineText(self, "Texto", "Digite o texto:")
        if ok and txt.strip():
            s = Shape("text", text=txt, font=self.font_combo.currentFont().family(),
                      size=self.size_spin.value(), fill="#000000", stroke=None, tx=sp.x(), ty=sp.y())
            self.add_shape(s)

    def edit_text(self, s):
        txt, ok = QInputDialog.getMultiLineText(self, "Editar texto", "Texto:", s.text)
        if ok and txt.strip() and txt != s.text:
            before = self.snapshot()
            s.text = txt
            self.sync(s)
            self.commit(before)

    # ------------------------------------------------------------ página
    def set_page(self, w, h):
        if abs(w - self.page_w) < 1e-6 and abs(h - self.page_h) < 1e-6:
            return
        before = self.snapshot()
        self.page_w, self.page_h = w, h
        self.update_scene_rect()
        self.commit(before)

    def on_page_preset(self, i):
        name = self.page_combo.itemText(i)
        if name in PAGES:
            w, h = PAGES[name]
            if self.page_w > self.page_h:
                w, h = h, w
            self.set_page(w, h)

    def on_page_custom(self):
        self.set_page(self.page_w_spin.value(), self.page_h_spin.value())

    def set_orientation(self, landscape):
        w, h = sorted((self.page_w, self.page_h))
        self.set_page(h, w) if landscape else self.set_page(w, h)

    def ask_page_size(self):
        w, ok = QInputDialog.getDouble(self, "Página", "Largura (mm):", self.page_w, 10, 5000, 1)
        if not ok:
            return
        h, ok = QInputDialog.getDouble(self, "Página", "Altura (mm):", self.page_h, 10, 5000, 1)
        if ok:
            self.set_page(w, h)

    def toggle_rulers(self):
        v = self.a_rulers.isChecked()
        for wdg in (self.hruler, self.vruler, self.corner):
            wdg.setVisible(v)

    # ---------------------------------------------------------- arquivos
    def confirm_discard(self):
        if not self.dirty:
            return True
        r = QMessageBox.question(self, APP, "Há alterações não salvas. Deseja salvar antes?",
                                 QMessageBox.StandardButton.Save | QMessageBox.StandardButton.Discard
                                 | QMessageBox.StandardButton.Cancel)
        if r == QMessageBox.StandardButton.Cancel:
            return False
        if r == QMessageBox.StandardButton.Save:
            return self.save()
        return True

    def load_doc(self, shapes, page, path):
        self.canvas.pen_nodes = []
        self.page_w, self.page_h = page
        self.shapes = shapes
        self.selection = []
        self.canvas.edit = None
        self.canvas.node_sel = None
        self.undo_stack.clear()
        self.redo_stack.clear()
        self.path = path
        self.rebuild()
        self.set_dirty(False)
        self.canvas.zoom_page()

    def new_doc(self):
        if self.confirm_discard():
            self.load_doc([], (210.0, 297.0), None)

    def open_doc(self):
        if not self.confirm_discard():
            return
        path, _ = QFileDialog.getOpenFileName(self, "Abrir desenho", "", f"Desenho Vetorial (*{EXT});;Todos (*.*)")
        if path:
            self.open_path(path)

    def open_path(self, path):
        try:
            with open(path, encoding="utf-8") as fh:
                data = json.load(fh)
            if data.get("version", 1) >= 2:
                shapes = [Shape.from_dict(d) for d in data["shapes"]]
                page = tuple(data.get("page", (210.0, 297.0)))
            else:
                shapes = convert_v1(data["shapes"])
                page = (210.0, 297.0)
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, APP, f"Não foi possível abrir o arquivo:\n{exc}")
            return False
        self.load_doc(shapes, page, path)
        return True

    def save(self):
        if not self.path:
            return self.save_as()
        return self.write(self.path)

    def save_as(self):
        path, _ = QFileDialog.getSaveFileName(self, "Salvar desenho", "desenho" + EXT, f"Desenho Vetorial (*{EXT})")
        if not path:
            return False
        if not path.lower().endswith(EXT):
            path += EXT
        return self.write(path)

    def write(self, path):
        data = {"app": APP, "version": 2, "page": [self.page_w, self.page_h],
                "shapes": [s.to_dict() for s in self.shapes]}
        try:
            with open(path, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False)
        except OSError as exc:
            QMessageBox.critical(self, APP, f"Não foi possível salvar:\n{exc}")
            return False
        self.path = path
        self.set_dirty(False)
        self.statusBar().showMessage("Salvo.", 3000)
        return True

    def export(self):
        path, flt = QFileDialog.getSaveFileName(self, "Exportar", "desenho.pdf",
                                                "PDF (*.pdf);;Imagem PNG (*.png);;SVG (*.svg)")
        if not path:
            return
        low = path.lower()
        if not low.endswith((".pdf", ".png", ".svg")):
            path += ".png" if "PNG" in flt else (".svg" if "SVG" in flt else ".pdf")
            low = path.lower()
        try:
            if low.endswith(".pdf"):
                self.export_pdf(path)
            elif low.endswith(".png"):
                dpi, ok = QInputDialog.getInt(self, "Exportar PNG", "Resolução (DPI):", 300, 36, 1200)
                if not ok:
                    return
                self.export_png(path, dpi)
            else:
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(self.to_svg())
        except Exception as exc:  # noqa: BLE001
            QMessageBox.critical(self, APP, f"Não foi possível exportar:\n{exc}")
            return
        self.statusBar().showMessage(f"Exportado: {path}", 5000)

    def page_rect(self):
        return QRectF(0, 0, self.page_w, self.page_h)

    def export_png(self, path, dpi):
        w = max(1, round(self.page_w / 25.4 * dpi))
        h = max(1, round(self.page_h / 25.4 * dpi))
        img = QImage(w, h, QImage.Format.Format_ARGB32)
        img.fill(QColor("white"))
        p = QPainter(img)
        p.setRenderHints(QPainter.RenderHint.Antialiasing | QPainter.RenderHint.TextAntialiasing)
        self.scene.render(p, QRectF(0, 0, w, h), self.page_rect())
        p.end()
        if not img.save(path, "PNG"):
            raise OSError("falha ao gravar o PNG")

    def export_pdf(self, path):
        wr = QPdfWriter(path)
        size = QSizeF(min(self.page_w, self.page_h), max(self.page_w, self.page_h))
        orient = QPageLayout.Orientation.Landscape if self.page_w > self.page_h else QPageLayout.Orientation.Portrait
        wr.setPageLayout(QPageLayout(QPageSize(size, QPageSize.Unit.Millimeter, "Página"), orient,
                                     QMarginsF(0, 0, 0, 0), QPageLayout.Unit.Millimeter))
        wr.setResolution(600)
        wr.setTitle(APP)
        p = QPainter(wr)
        p.setRenderHint(QPainter.RenderHint.Antialiasing)
        self.scene.render(p, QRectF(0, 0, wr.width(), wr.height()), self.page_rect())
        p.end()

    def to_svg(self):
        W, H = self.page_w, self.page_h
        out = ['<?xml version="1.0" encoding="UTF-8"?>',
               f'<svg xmlns="http://www.w3.org/2000/svg" width="{W:.3f}mm" height="{H:.3f}mm" '
               f'viewBox="0 0 {W:.3f} {H:.3f}">']
        for s in self.shapes:
            tr = ""
            if s.tx or s.ty or s.angle:
                tr = f' transform="translate({s.tx:.4f} {s.ty:.4f}) rotate({s.angle:.4f})"'
            stroke = (f'stroke="{s.stroke}" stroke-width="{s.stroke_w:.4f}" stroke-miterlimit="4"'
                      if s.stroke and s.stroke_w > 0 else 'stroke="none"')
            fill = s.fill or "none"
            if s.kind == "rect":
                rr = max(0.0, min(s.radius, abs(s.w) / 2, abs(s.h) / 2))
                rx = f' rx="{rr:.4f}"' if rr else ""
                out.append(f'  <rect x="{s.x:.4f}" y="{s.y:.4f}" width="{s.w:.4f}" height="{s.h:.4f}"{rx} '
                           f'fill="{fill}" {stroke}{tr}/>')
            elif s.kind == "ellipse":
                out.append(f'  <ellipse cx="{s.x + s.w / 2:.4f}" cy="{s.y + s.h / 2:.4f}" rx="{s.w / 2:.4f}" '
                           f'ry="{s.h / 2:.4f}" fill="{fill}" {stroke}{tr}/>')
            elif s.kind == "path":
                if s.fill and not all(sp["closed"] for sp in s.paths):
                    closed = [sp for sp in s.paths if sp["closed"]]
                    if closed:
                        out.append(f'  <path d="{svg_d(closed)}" fill="{fill}" fill-rule="evenodd" stroke="none"{tr}/>')
                    out.append(f'  <path d="{svg_d(s.paths)}" fill="none" {stroke}{tr}/>')
                else:
                    out.append(f'  <path d="{svg_d(s.paths)}" fill="{fill}" fill-rule="evenodd" {stroke}{tr}/>')
            elif s.kind == "text":
                font = QFont(s.font)
                font.setPixelSize(100)
                fm = QFontMetricsF(font)
                k = s.size * PT_MM / 100
                lines = []
                for i, line in enumerate(s.text.split("\n")):
                    y = s.y + (fm.ascent() + i * fm.lineSpacing()) * k
                    lines.append(f'<tspan x="{s.x:.4f}" y="{y:.4f}" xml:space="preserve">{escape(line)}</tspan>')
                out.append(f'  <text font-family="{escape(s.font)}" font-size="{100 * k:.4f}" fill="{fill}" '
                           f'{stroke}{tr}>{"".join(lines)}</text>')
        out.append("</svg>")
        return "\n".join(out) + "\n"

    # -------------------------------------------------------------- ajuda
    def show_help(self):
        QMessageBox.information(self, "Atalhos e dicas", (
            "<b>Ferramentas</b><br>"
            "V Seleção · F10 Forma · Z Zoom · H Mão · F5 Mão livre · P Caneta<br>"
            "F6 Retângulo · F7 Elipse · Y Polígono · F8 Texto<br><br>"
            "<b>Caneta (Bézier)</b><br>"
            "Clique = nó de canto · Clique e arraste = curva suave<br>"
            "Clique no primeiro nó = fecha a curva · Enter, Esc ou duplo clique = termina<br>"
            "Backspace = remove o último nó · Botão direito = termina<br><br>"
            "<b>Forma (editar nós)</b><br>"
            "Arraste nós e alças · Duplo clique na linha = adiciona nó · Duplo clique no nó = exclui<br>"
            "Del = exclui o nó · Botões Suave/Cúspide/Linha/Curva na barra de propriedades<br>"
            "Retângulos, elipses e textos: Ctrl+Q para converter em curvas<br><br>"
            "<b>Seleção</b><br>"
            "Shift+clique soma · Arraste no vazio = seleção por área<br>"
            "Clique de novo no objeto selecionado = modo girar · Ctrl = passos de 15°<br>"
            "Alças de canto = proporcional (Ctrl = livre) · Shift = a partir do centro<br>"
            "Setas = 1 mm · Shift+setas = 10 mm · Ctrl+setas = 0,1 mm<br><br>"
            "<b>Zoom</b><br>"
            "Roda do mouse = zoom · Botão do meio ou Espaço+arrastar = mover a vista<br>"
            "F4 = todos os objetos · Shift+F4 = página · Shift+F2 = seleção · Ctrl+1 = 100%<br><br>"
            "<b>Cores</b><br>"
            "Paleta à direita: clique = preenchimento · botão direito = contorno · X = nenhum<br><br>"
            "<b>Alinhar</b> (2+ objetos entre si, 1 objeto na página)<br>"
            "L esquerda · R direita · T topo · B base · C centro vertical · E centro horizontal"))

    def closeEvent(self, e):
        if self.confirm_discard():
            e.accept()
        else:
            e.ignore()


def svg_d(subs):
    parts = []
    for sp in subs:
        nodes = sp["nodes"]
        if not nodes:
            continue
        parts.append(f"M{nodes[0]['x']:.4f} {nodes[0]['y']:.4f}")
        n = len(nodes)
        segs = n if sp["closed"] and n > 1 else n - 1
        for i in range(segs):
            a, b = nodes[i], nodes[(i + 1) % n]
            if a["out"] is None and b["in"] is None:
                parts.append(f"L{b['x']:.4f} {b['y']:.4f}")
            else:
                _, c1, c2, e = seg_ctrl(a, b)
                parts.append(f"C{c1[0]:.4f} {c1[1]:.4f} {c2[0]:.4f} {c2[1]:.4f} {e[0]:.4f} {e[1]:.4f}")
        if sp["closed"]:
            parts.append("Z")
    return " ".join(parts)


def convert_v1(old):
    """Converte desenhos da primeira versão (pixels) para a atual (mm)."""
    k = 25.4 / 96
    out = []
    for s in old:
        t = s.get("type")
        co = [v * k for v in s.get("coords", [])]
        stroke = s.get("stroke") or None
        fill = s.get("fill") or None
        w = s.get("width", 1) * k
        if t in ("rect", "oval") and len(co) == 4:
            out.append(Shape("rect" if t == "rect" else "ellipse", x=min(co[0], co[2]), y=min(co[1], co[3]),
                             w=abs(co[2] - co[0]), h=abs(co[3] - co[1]), fill=fill, stroke=stroke, stroke_w=w))
        elif t in ("line", "pen") and len(co) >= 4:
            nodes = [node(co[i], co[i + 1]) for i in range(0, len(co) - 1, 2)]
            out.append(Shape("path", paths=[{"nodes": nodes, "closed": False}], fill=None, stroke=stroke, stroke_w=w))
        elif t == "text" and len(co) >= 2:
            out.append(Shape("text", text=s.get("text", ""), size=s.get("size", 18) * 0.75,
                             fill=stroke or "#000000", stroke=None, tx=co[0], ty=co[1]))
    return out


def dark_palette():
    p = QPalette()
    c = QColor
    p.setColor(QPalette.ColorRole.Window, c("#2b2b2b"))
    p.setColor(QPalette.ColorRole.WindowText, c("#e0e0e0"))
    p.setColor(QPalette.ColorRole.Base, c("#1f1f1f"))
    p.setColor(QPalette.ColorRole.AlternateBase, c("#2a2a2a"))
    p.setColor(QPalette.ColorRole.Text, c("#e0e0e0"))
    p.setColor(QPalette.ColorRole.Button, c("#333333"))
    p.setColor(QPalette.ColorRole.ButtonText, c("#e0e0e0"))
    p.setColor(QPalette.ColorRole.Highlight, c("#2f7fd6"))
    p.setColor(QPalette.ColorRole.HighlightedText, c("#ffffff"))
    p.setColor(QPalette.ColorRole.ToolTipBase, c("#333333"))
    p.setColor(QPalette.ColorRole.ToolTipText, c("#e0e0e0"))
    p.setColor(QPalette.ColorRole.PlaceholderText, c("#888888"))
    for role in (QPalette.ColorRole.Text, QPalette.ColorRole.ButtonText, QPalette.ColorRole.WindowText):
        p.setColor(QPalette.ColorGroup.Disabled, role, c("#777777"))
    return p


STYLE = """
QToolBar { background:#2d2d2d; border:0; spacing:2px; padding:2px; }
QToolBar::separator { background:#444; width:1px; height:1px; margin:4px; }
QToolButton { padding:3px; border-radius:3px; }
QToolButton:hover { background:#3c3c3c; }
QToolButton:checked { background:#2f6db3; }
QMenuBar { background:#2b2b2b; }
QMenuBar::item:selected, QMenu::item:selected { background:#2f6db3; }
QStatusBar { background:#252525; }
QDockWidget::title { background:#2d2d2d; padding:5px; }
QGroupBox { border:1px solid #3d3d3d; border-radius:4px; margin-top:10px; padding-top:6px; }
QGroupBox::title { subcontrol-origin: margin; left:8px; padding:0 3px; color:#bbb; }
QPushButton { background:#363636; border:1px solid #474747; border-radius:3px; padding:4px 8px; }
QPushButton:hover { background:#404040; }
QTabWidget::pane { border:1px solid #3d3d3d; }
QTabBar::tab { background:#2d2d2d; padding:6px 12px; }
QTabBar::tab:selected { background:#3a3a3a; }
"""


def main():
    QLocale.setDefault(QLocale("pt_BR"))
    app = QApplication(sys.argv)
    app.setApplicationName(APP)
    app.setStyle("Fusion")
    app.setPalette(dark_palette())
    app.setStyleSheet(STYLE)
    win = MainWindow()
    win.setWindowIcon(make_icon("pen", "#4aa3ff"))
    win.show()
    if len(sys.argv) > 1:
        win.open_path(sys.argv[1])
    sys.exit(app.exec())


if __name__ == "__main__":
    main()

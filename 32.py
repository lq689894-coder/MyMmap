#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import sys, json, math, io, os, re
import networkx as nx
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Tuple, Optional, Iterable, Union
from functools import wraps  # performance_monitor装饰器需要
import time  # performance_monitor装饰器需要
import logging  # 日志系统需要
import traceback  # show_detailed_error方法需要
from collections import defaultdict  # _SpatialHash和MindMapScene需要

from PyQt5.QtCore import (
    Qt, QTimer, QPoint, QByteArray, pyqtSignal, QEvent, QSettings, 
    QPointF, QRectF, QDateTime
)
from PyQt5.QtGui import (
    QFont, QColor, QPalette, QFontDatabase, QKeySequence, QIcon, 
    QPainter, QPen, QBrush, QLinearGradient, QPainterPath, QTransform, QGuiApplication, QFontMetrics
)
from PyQt5.QtWidgets import (
    QApplication, QMainWindow, QWidget, QSplitter, QTextEdit,
    QVBoxLayout, QFileDialog, QStatusBar, QMessageBox,
    QMenu, QTreeWidgetItem, QAbstractItemView, QTreeWidget, QStyledItemDelegate,
    QInputDialog, QFontDialog, QAction, QShortcut, QDialog,  QHBoxLayout, QLabel, QTabWidget,
    QGroupBox, QFormLayout, QSpinBox, QDoubleSpinBox, QPushButton, QScrollArea,
    QLineEdit,  QFrame, QSlider, QCheckBox, QToolButton, QStyle, QGraphicsScene, 
    QGraphicsItem, QGraphicsObject, QGraphicsTextItem, QColorDialog, QGraphicsPathItem, 
    QListWidget, QListWidgetItem, QDialogButtonBox, QGraphicsLineItem, QGraphicsView
)


class _SpatialHash:
    def __init__(self, cell=120):
        from collections import defaultdict
        self.cell = max(40, int(cell))
        self.grid = defaultdict(set)   # (ix,iy) -> {name}
        self.radius = {}               # name -> approx radius

    def _keys_for(self, x, y, r):
        c = self.cell
        x0 = int((x - r) // c); x1 = int((x + r) // c)
        y0 = int((y - r) // c); y1 = int((y + r) // c)
        for ix in range(x0, x1 + 1):
            for iy in range(y0, y1 + 1):
                yield (ix, iy)

    def insert(self, name, x, y, r):
        self.radius[name] = float(r)
        for key in self._keys_for(x, y, r):
            self.grid[key].add(name)

    def remove(self, name, x, y):
        r = self.radius.get(name, 0.0)
        for key in list(self._keys_for(x, y, r)):
            s = self.grid.get(key)
            if s:
                s.discard(name)
                if not s:
                    self.grid.pop(key, None)
        self.radius.pop(name, None)

    def move(self, name, oldx, oldy, newx, newy):
        r = self.radius.get(name, 0.0)
        old_keys = set(self._keys_for(oldx, oldy, r))
        new_keys = set(self._keys_for(newx, newy, r))
        for key in old_keys - new_keys:
            s = self.grid.get(key)
            if s:
                s.discard(name)
                if not s:
                    self.grid.pop(key, None)
        for key in new_keys - old_keys:
            self.grid.setdefault(key, set()).add(name)

    def neighbors(self, x, y, r):
        hits = set()
        for key in self._keys_for(x, y, r):
            hits |= self.grid.get(key, set())
        return hits


# 配置日志系统
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.FileHandler(str(Path.home() / ".mindmap_debug.log"), encoding='utf-8'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger("MindMap")

# 使用实例变量替代全局常量
AUTOSAVE_PATH = str(Path.home() / ".mindmap_autosave.json")
SETTINGS_PATH = str(Path.home() / ".mindmap_settings.json")

# -----------------------------------------------------------
# 小工具
# -----------------------------------------------------------
APP_SETTINGS_PATH = str(Path.home() / ".mindmap_settings.json")


# ---------------------------- 大纲视图参数配置 ----------------------------
TITLE_ROLE = Qt.UserRole + 1
DEPTH_ROLE = Qt.UserRole + 2
INDENT_SPACES = 4
DEBOUNCE_MS_EDITOR_TO_TREE = 300

BULLET_PREFIXES = ["- ", "* ", "+ "]
LEVEL_COLORS_LIGHT = ["#ef4444", "#f59e0b", "#84cc16", "#06b6d4", "#8b5cf6", "#ec4899"]

ACCENTS = {
    "珊瑚红": "#ff6b6b", "活力橙": "#fd7e14", "柠檬黄": "#ffd43b",
    "草原绿": "#40c057", "天空蓝": "#339af0", "薰衣草": "#cc5de8", "彩虹": "#ff6b6b"
}


# -------------------------- 性能监控装饰器 --------------------------
def performance_monitor(func):
    @wraps(func)
    def wrapper(*args, **kwargs):
        start_time = time.time()
        try:
            result = func(*args, **kwargs)
            elapsed = time.time() - start_time
            if elapsed > 0.1:  # 只记录耗时较长的操作
                logger.debug(f"PERF: {func.__name__} took {elapsed:.3f}s")
            return result
        except Exception as e:
            elapsed = time.time() - start_time
            logger.error(f"PERF_ERROR: {func.__name__} failed after {elapsed:.3f}s: {e}")
            # 重新抛出原始异常，保持调用栈
            raise
    return wrapper

def error_handler(message_prefix=""):
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            try:
                return func(*args, **kwargs)
            except Exception as e:
                error_msg = f"{message_prefix}: {str(e)}"
                logger.error(f"ERROR in {func.__name__}: {error_msg}", exc_info=True)
                # 在开发阶段显示详细错误信息
                if hasattr(args[0], 'show_detailed_error'):
                    args[0].show_detailed_error(f"{func.__name__} 操作失败", error_msg)
                else:
                    QMessageBox.critical(None, "错误", f"{message_prefix}\n\n详细错误: {str(e)}")
                raise
        return wrapper
    return decorator

# ---------------------------- 现代化设置对话框 ----------------------------

# -----------------------------------------------------------
# 预览卡（强化版）
# -----------------------------------------------------------

def clamp(v: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, v))


class _PreviewCard(QWidget):
    """右侧实时预览：两节点 + 一条曲线边 + 背景网格，可缩放/暗色主题。
    setParameters(params: dict) 可随时更新。
    """
    def __init__(self, parent=None):
        super().__init__(parent)
        # 增大预览区域尺寸
        self.setMinimumSize(400, 350)
        self.setObjectName("PreviewCard")
        self._params: Dict[str, float] = {
            "NODE_FONT_SIZE": 12,
            "NODE_PADDING_X": 8,
            "NODE_PADDING_Y": 6,
            "NODE_CORNER_RADIUS": 12,
            "EDGE_LENGTH_FACTOR": 1.0,
            "SNAP_STEP": 40,
            "EDGE_CONTROL_POINT_RATIO": 0.15,
            "EDGE_BEND_RATIO": 0.05,
        }
        self._dark = False
        self._zoom = 1.0
        # 添加更多预览元素
        self._show_grid = True
        self._show_edge_controls = True

    def setDark(self, on: bool):
        self._dark = bool(on)
        self.update()

    def setZoom(self, z: float):
        self._zoom = clamp(z, 0.5, 2.0)
        self.update()

    def setParameters(self, params: dict):
        self._params.update(params)
        self.update()

    def toggleGrid(self, show: bool):
        self._show_grid = bool(show)
        self.update()
        
    def toggleEdgeControls(self, show: bool):
        self._show_edge_controls = bool(show)
        self.update()

    # --- 绘制 ---
    def _node_rect(self, text: str, center: Tuple[float, float]):
        from PyQt5.QtGui import QFontMetrics
        font = QFont("Segoe UI", int(self._params.get("NODE_FONT_SIZE", 12)), QFont.Medium)
        fm = QFontMetrics(font)
        w = fm.horizontalAdvance(text)
        h = fm.height()
        px = int(self._params.get("NODE_PADDING_X", 8))
        py = int(self._params.get("NODE_PADDING_Y", 6))
        rect_w = w + 2 * px
        rect_h = h + 2 * py
        cx, cy = center
        return QRectF(cx - rect_w/2, cy - rect_h/2, rect_w, rect_h), font

    def paintEvent(self, _):
        p = QPainter(self)
        p.setRenderHint(QPainter.Antialiasing, True)

        # 画背景
        if self._dark:
            bg = QColor(22, 27, 34)
            grid = QColor(62, 67, 74)
            control_color = QColor(255, 200, 100, 180)
        else:
            bg = QColor(248, 250, 253)
            grid = QColor(226, 232, 240)
            control_color = QColor(255, 150, 50, 180)
        p.fillRect(self.rect(), bg)

        # 网格（可选）
        if self._show_grid:
            step = clamp(float(self._params.get("SNAP_STEP", 40)), 10, 80)
            pen_grid = QPen(grid)
            pen_grid.setCosmetic(True)
            p.setPen(pen_grid)
            s = int(step)
            for x in range(0, self.width(), s):
                p.drawLine(x, 0, x, self.height())
            for y in range(0, self.height(), s):
                p.drawLine(0, y, self.width(), y)

        # 两个示例节点位置（随缩放）
        zoom = self._zoom
        p1 = (int(100*zoom), int(100*zoom))
        p2 = (int(300*zoom), int(250*zoom))

        # 贝塞尔连线
        path = QPainterPath(QPointF(*p1))
        dx = p2[0] - p1[0]; dy = p2[1] - p1[1]
        d = max(1.0, (dx*dx + dy*dy) ** 0.5)
        ux, uy = dx / d, dy / d
        nx_, ny_ = -uy, ux
        
        # 使用参数控制曲线形状
        edge_length_factor = float(self._params.get("EDGE_LENGTH_FACTOR", 1.0))
        control_point_ratio = float(self._params.get("EDGE_CONTROL_POINT_RATIO", 0.15))
        bend_ratio = float(self._params.get("EDGE_BEND_RATIO", 0.05))
        
        t = d * control_point_ratio * edge_length_factor
        b = min(36.0, d * bend_ratio * edge_length_factor)
        c1 = QPointF(p1[0] + ux * t + nx_ * b, p1[1] + uy * t + ny_ * b)
        c2 = QPointF(p2[0] - ux * t + nx_ * b, p2[1] - uy * t + ny_ * b)
        path.cubicTo(c1, c2, QPointF(*p2))

        pen_edge = QPen(QColor(140, 140, 140) if not self._dark else QColor(198, 205, 213), 2)
        pen_edge.setCosmetic(True)
        p.setPen(pen_edge)
        p.setBrush(Qt.NoBrush)
        p.drawPath(path)
        
        # 显示控制点（可选）
        if self._show_edge_controls:
            # 控制点连线
            pen_control_line = QPen(control_color, 1, Qt.DashLine)
            pen_control_line.setCosmetic(True)
            p.setPen(pen_control_line)
            p.drawLine(QPointF(*p1), c1)
            p.drawLine(c1, c2)
            p.drawLine(c2, QPointF(*p2))
            
            # 控制点
            p.setBrush(QBrush(control_color))
            p.setPen(QPen(control_color, 1))
            control_radius = 4
            p.drawEllipse(c1, control_radius, control_radius)
            p.drawEllipse(c2, control_radius, control_radius)

        # 画两个圆角节点
        r1, f1 = self._node_rect("父节点", p1)
        r2, f2 = self._node_rect("子节点", p2)
        radius = int(self._params.get("NODE_CORNER_RADIUS", 12))

        def draw_node(r: QRectF, font: QFont, base_color: QColor, text: str):
            # 阴影
            p.setPen(Qt.NoPen)
            p.setBrush(QColor(0, 0, 0, 55 if not self._dark else 120))
            p.drawRoundedRect(r.translated(2, 3), radius, radius)
            # 渐变
            grad = QLinearGradient(r.topLeft(), r.bottomRight())
            lighter = QColor(base_color).lighter(135)
            darker = QColor(base_color).darker(125)
            if self._dark:
                lighter = lighter.darker(110); darker = darker.darker(130)
            grad.setColorAt(0.0, lighter)
            grad.setColorAt(1.0, darker)
            p.setBrush(grad)
            p.setPen(QPen(QColor(30, 70, 120) if not self._dark else QColor(120, 170, 255), 2))
            p.drawRoundedRect(r, radius, radius)
            # 文本
            p.setFont(font)
            p.setPen(QColor(20, 20, 20) if not self._dark else QColor(240, 242, 244))
            fm = p.fontMetrics()
            tw = fm.horizontalAdvance(text); th = fm.height()
            p.drawText(QPointF(r.center().x() - tw/2, r.center().y() + th/4 - 2), text)

        base = QColor(173, 216, 230)
        draw_node(r1, f1, base, "父节点")
        draw_node(r2, f2, base, "子节点")

        # 右下角小注记
        p.setPen(QPen(QColor(120, 130, 140) if not self._dark else QColor(155, 165, 175)))
        p.setFont(QFont("Segoe UI", 9))
        p.drawText(self.rect().adjusted(8, 8, -8, -8), Qt.AlignRight | Qt.AlignBottom,
                   f"预览 ×{self._zoom:.2f}")
                   
        # 显示当前参数值
        param_text = f"字体: {self._params.get('NODE_FONT_SIZE', 12)}px\n"
        param_text += f"边曲率: {self._params.get('EDGE_CONTROL_POINT_RATIO', 0.15):.2f}"
        p.drawText(self.rect().adjusted(8, 8, -8, -8), Qt.AlignLeft | Qt.AlignTop, param_text)


# -----------------------------------------------------------
# SettingsDialog（升级版）
# -----------------------------------------------------------
class SettingsDialog(QDialog):
    defaults_applied = pyqtSignal(dict)          # 运行期默认值（仅影响此后新增节点）
    apply_to_existing = pyqtSignal(dict)         # 可选：应用到现有节点（父窗口可连接）

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("思维导图参数设置（增强预览版）")
        # 增大窗口尺寸以容纳更大的预览
        self.resize(1580, 850)
        self.setMinimumSize(1580, 850)

        # 顶部：搜索 + 预设 + 导入导出 + 暗色切换
        topbar = QHBoxLayout()
        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("搜索参数（按名称/分组）…")
        self.search_edit.textChanged.connect(self._on_search)

        self.dark_toggle = QCheckBox("暗色预览")
        self.dark_toggle.stateChanged.connect(lambda s: self.preview.setDark(s == Qt.Checked))

        self.live_preview_toggle = QCheckBox("实时预览")
        self.live_preview_toggle.setChecked(True)
        
        # 新增预览控制选项
        self.grid_toggle = QCheckBox("显示网格")
        self.grid_toggle.setChecked(True)
        self.grid_toggle.stateChanged.connect(lambda s: self.preview.toggleGrid(s == Qt.Checked))
        
        self.controls_toggle = QCheckBox("显示控制点")
        self.controls_toggle.setChecked(True)
        self.controls_toggle.stateChanged.connect(lambda s: self.preview.toggleEdgeControls(s == Qt.Checked))

        btn_save = QToolButton(); btn_save.setText("导出JSON"); btn_save.clicked.connect(self._export_json)
        btn_load = QToolButton(); btn_load.setText("导入JSON"); btn_load.clicked.connect(self._import_json)

        btn_reset_all = QToolButton(); btn_reset_all.setText("恢复全部默认"); btn_reset_all.clicked.connect(self.restore_defaults)

        topbar.addWidget(self.search_edit, 1)
        topbar.addWidget(self.dark_toggle)
        topbar.addWidget(self.live_preview_toggle)
        topbar.addWidget(self.grid_toggle)
        topbar.addWidget(self.controls_toggle)
        topbar.addWidget(btn_load)
        topbar.addWidget(btn_save)
        topbar.addWidget(btn_reset_all)

        # 主体：左侧 Tab + 右侧预览
        self.tab_widget = QTabWidget(); self.tab_widget.setDocumentMode(True)

        left = QVBoxLayout(); left.addLayout(topbar); left.addWidget(self.tab_widget, 1)
        left_w = QWidget(); left_w.setLayout(left)

        # 右侧预览与控制条 - 增大预览区域
        self.preview = _PreviewCard(self)
        
        # 预览控制区域
        preview_controls = QVBoxLayout()
        
        # 缩放控制
        zoom_layout = QHBoxLayout()
        zoom_layout.addWidget(QLabel("预览缩放:"))
        self.zoom_slider = QSlider(Qt.Horizontal)
        self.zoom_slider.setRange(50, 200)
        self.zoom_slider.setValue(100)
        self.zoom_slider.valueChanged.connect(lambda v: self.preview.setZoom(v/100.0))
        zoom_layout.addWidget(self.zoom_slider)
        self.zoom_label = QLabel("1.00x")
        self.zoom_slider.valueChanged.connect(lambda v: self.zoom_label.setText(f"{v/100.0:.2f}x"))
        zoom_layout.addWidget(self.zoom_label)
        
        # 重置预览按钮
        self.reset_preview_btn = QPushButton("重置预览视角")
        self.reset_preview_btn.clicked.connect(lambda: self.zoom_slider.setValue(100))
        
        preview_controls.addLayout(zoom_layout)
        preview_controls.addWidget(self.reset_preview_btn)
        
        # 预览区域
        preview_box = QVBoxLayout()
        preview_box.addWidget(QLabel("实时预览:"), 0)
        preview_box.addWidget(self.preview, 1)
        preview_box.addLayout(preview_controls)

        right_w = QWidget(); 
        right_w.setLayout(preview_box)
        # 设置右侧区域的最小宽度
        right_w.setMinimumWidth(450)

        # 底部按钮
        btns = QHBoxLayout(); btns.addStretch(1)
        self.btn_restore_tab = QPushButton("↺ 仅此页")
        self.btn_restore_tab.clicked.connect(self.restore_current_tab_defaults)
        self.btn_apply = QPushButton("应用")
        self.btn_apply.clicked.connect(self.apply_current_values)
        self.btn_ok = QPushButton("确定")
        self.btn_ok.clicked.connect(self.accept)
        self.btn_cancel = QPushButton("取消")
        self.btn_cancel.clicked.connect(self.reject)
        # 可选：一键应用到已存在节点
        self.apply_existing_chk = QCheckBox("同时应用到现有节点")

        btns.addWidget(self.apply_existing_chk)
        btns.addWidget(self.btn_restore_tab)
        btns.addWidget(self.btn_cancel)
        btns.addWidget(self.btn_apply)
        btns.addWidget(self.btn_ok)

        # 布局拼装 - 使用容器避免布局冲突
        main_container = QWidget()
        main_layout = QHBoxLayout(main_container)
        main_layout.addWidget(left_w, 1)
        main_layout.addWidget(vsep(), 0)
        main_layout.addWidget(right_w, 1)  # 让右侧也有弹性空间
        
        outer_layout = QVBoxLayout()
        outer_layout.addWidget(main_container, 1)
        outer_layout.addLayout(btns)
        
        self.setLayout(outer_layout)

        # 构建各 Tab
        self._build_tabs()

        # 设置实时预览
        self._setup_real_time_preview()

        # 现代样式
        self._apply_modern_style()

        # 首次渲染
        self._on_any_value_changed()

    # ---------------- 实时预览连接 ----------------
    def _setup_real_time_preview(self):
        """设置所有控件的实时预览连接"""
        # 获取所有数值控件并连接信号
        controls = [
            self.target_edge_spin, self.min_chord_ratio_spin, self.max_extra_stretch_spin,
            self.edge_length_factor_spin, self.spatial_hash_cell_spin, self.min_node_distance_spin,
            self.node_font_size_spin, self.node_padding_x_spin, self.node_padding_y_spin,
            self.node_corner_radius_spin, self.edge_base_radius_spin, self.edge_ring_spacing_spin,
            self.edge_control_point_ratio_spin, self.edge_bend_ratio_spin, self.radial_base_r_spin,
            self.radial_max_cone_spin, self.radial_pad_arc_spin, self.radial_stretch_step_spin,
            self.snap_step_spin, self.align_threshold_spin, self.history_limit_spin,
            self.autosave_delay_spin
        ]
        
        for control in controls:
            # 移除之前的连接（避免重复）
            try:
                control.valueChanged.disconnect()
            except:
                pass
            # 重新连接
            control.valueChanged.connect(self._on_any_value_changed)

    # ---------------- UI 组装 ----------------
    def _build_tabs(self):
        self._groups = []  # 用于搜索过滤

        self._tab_layout = self._make_tab_layout()
        self._tab_node = self._make_tab_node()
        self._tab_edge = self._make_tab_edge()
        self._tab_arr = self._make_tab_arrangement()
        self._tab_view = self._make_tab_view()
        self._tab_perf = self._make_tab_performance()

        self.tab_widget.addTab(self._scroll(self._tab_layout), "📐 布局")
        self.tab_widget.addTab(self._scroll(self._tab_node),   "🔘 节点")
        self.tab_widget.addTab(self._scroll(self._tab_edge),   "🔗 边")
        self.tab_widget.addTab(self._scroll(self._tab_arr),    "🔄 排列")
        self.tab_widget.addTab(self._scroll(self._tab_view),   "👁️ 视图")
        self.tab_widget.addTab(self._scroll(self._tab_perf),   "⚡ 性能")

    def _scroll(self, w: QWidget) -> QScrollArea:
        s = QScrollArea(); s.setWidgetResizable(True); s.setWidget(w); return s

    # --- 一些工厂方法 ---
    def _group(self, title: str) -> QGroupBox:
        g = QGroupBox(title)
        self._groups.append(g)
        return g

    def _spin(self, minv: int, maxv: int, defv: int, suffix: Optional[str] = None) -> QSpinBox:
        sp = QSpinBox(); sp.setRange(minv, maxv); sp.setValue(defv)
        if suffix: sp.setSuffix(" " + suffix)
        sp.valueChanged.connect(self._on_any_value_changed)
        return sp

    def _dspin(self, minv: float, maxv: float, defv: float, step: float, decimals=2, suffix: Optional[str] = None) -> QDoubleSpinBox:
        sp = QDoubleSpinBox(); sp.setRange(minv, maxv); sp.setValue(defv); sp.setSingleStep(step); sp.setDecimals(decimals)
        if suffix: sp.setSuffix(" " + suffix)
        sp.valueChanged.connect(self._on_any_value_changed)
        return sp

    def _spin_with_slider(self, minv: int, maxv: int, defv: int, suffix: str | None = None) -> Tuple[QSpinBox, QSlider, QWidget]:
        sp = self._spin(minv, maxv, defv, suffix)
        sl = QSlider(Qt.Horizontal); sl.setRange(minv, maxv); sl.setValue(defv)
        sl.valueChanged.connect(sp.setValue)
        sp.valueChanged.connect(sl.setValue)
        box = QHBoxLayout(); box.addWidget(sp); box.addWidget(sl, 1)
        w = QWidget(); w.setLayout(box)
        return sp, sl, w

    def _dspin_with_slider(self, minv: float, maxv: float, defv: float, step: float, decimals=2, suffix: str | None = None) -> Tuple[QDoubleSpinBox, QSlider, QWidget]:
        scale = 10 ** decimals
        sp = self._dspin(minv, maxv, defv, step, decimals, suffix)
        sl = QSlider(Qt.Horizontal); sl.setRange(int(minv*scale), int(maxv*scale)); sl.setValue(int(defv*scale))
        sl.valueChanged.connect(lambda v: sp.setValue(v/scale))
        sp.valueChanged.connect(lambda v: sl.setValue(int(v*scale)))
        box = QHBoxLayout(); box.addWidget(sp); box.addWidget(sl, 1)
        w = QWidget(); w.setLayout(box)
        return sp, sl, w

    # --- 各 Tab ---
    def _make_tab_layout(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g_basic = self._group("基本布局参数")
        f = QFormLayout(g_basic); f.setVerticalSpacing(12); f.setHorizontalSpacing(18)

        # 从父窗口读取默认值（若无则给默认）
        p = self.parent() or object()
        self.target_edge_spin, _, w1 = self._spin_with_slider(120, 320, getattr(p, 'TARGET_EDGE', 180), "像素")
        self.min_chord_ratio_spin, _, w2 = self._dspin_with_slider(0.5, 0.95, getattr(p, 'MIN_CHORD_RATIO', 0.8), 0.01, 2)
        self.max_extra_stretch_spin, _, w3 = self._dspin_with_slider(1.0, 5.0, getattr(p, 'MAX_EXTRA_STRETCH', 3.0), 0.1, 1, "倍边长")
        self.edge_length_factor_spin, _, w4 = self._dspin_with_slider(0.3, 3.0, getattr(p, 'EDGE_LENGTH_FACTOR', 1.0), 0.1, 1)
        f.addRow("目标边长:", w1)
        f.addRow("弦长占比:", w2)
        f.addRow("最大附加拉伸:", w3)
        f.addRow("连线长度系数:", w4)

        g_adv = self._group("高级布局参数")
        f2 = QFormLayout(g_adv); f2.setVerticalSpacing(12); f2.setHorizontalSpacing(18)
        self.spatial_hash_cell_spin, _, w5 = self._spin_with_slider(40, 240, getattr(p, 'SPATIAL_HASH_CELL_SIZE', 120), "像素")
        self.min_node_distance_spin, _, w6 = self._spin_with_slider(80, 240, getattr(p, 'MIN_NODE_DISTANCE', 140), "像素")
        f2.addRow("空间哈希网格大小:", w5)
        f2.addRow("最小节点距离:", w6)

        lay.addWidget(g_basic); lay.addWidget(g_adv); lay.addStretch(1)
        return tab

    def _make_tab_node(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g_text = self._group("文本参数")
        f = QFormLayout(g_text)
        self.node_font_size_spin, _, w1 = self._spin_with_slider(8, 24, getattr(self.parent(), 'NODE_FONT_SIZE', 12), "像素")
        f.addRow("节点字体大小:", w1)

        g_size = self._group("尺寸参数")
        f2 = QFormLayout(g_size)
        self.node_padding_x_spin, _, w2 = self._spin_with_slider(4, 28, getattr(self.parent(), 'NODE_PADDING_X', 8), "像素")
        self.node_padding_y_spin, _, w3 = self._spin_with_slider(2, 24, getattr(self.parent(), 'NODE_PADDING_Y', 6), "像素")
        self.node_corner_radius_spin, _, w4 = self._spin_with_slider(4, 28, getattr(self.parent(), 'NODE_CORNER_RADIUS', 12), "像素")
        f2.addRow("水平内边距:", w2)
        f2.addRow("垂直内边距:", w3)
        f2.addRow("圆角半径:", w4)

        lay.addWidget(g_text); lay.addWidget(g_size); lay.addStretch(1)
        return tab

    def _make_tab_edge(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g_geo = self._group("几何参数")
        f = QFormLayout(g_geo)
        self.edge_base_radius_spin, _, w1 = self._dspin_with_slider(50.0, 240.0, getattr(self.parent(), 'EDGE_BASE_RADIUS', 160.0), 10.0, 1, "像素")
        self.edge_ring_spacing_spin, _, w2 = self._dspin_with_slider(80.0, 280.0, getattr(self.parent(), 'EDGE_RING_SPACING', 160.0), 10.0, 1, "像素")
        f.addRow("基础半径:", w1)
        f.addRow("环间距:", w2)

        g_curve = self._group("曲线参数")
        f2 = QFormLayout(g_curve)
        self.edge_control_point_ratio_spin, _, w3 = self._dspin_with_slider(0.05, 0.30, getattr(self.parent(), 'EDGE_CONTROL_POINT_RATIO', 0.15), 0.01, 2)
        self.edge_bend_ratio_spin, _, w4 = self._dspin_with_slider(0.01, 0.10, getattr(self.parent(), 'EDGE_BEND_RATIO', 0.05), 0.01, 2)
        f2.addRow("控制点比例:", w3)
        f2.addRow("弯曲比例:", w4)

        lay.addWidget(g_geo); lay.addWidget(g_curve); lay.addStretch(1)
        return tab

    def _make_tab_arrangement(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g = self._group("径向排列参数")
        f = QFormLayout(g)
        self.radial_base_r_spin, _, w1 = self._dspin_with_slider(40.0, 200.0, getattr(self.parent(), 'RADIAL_BASE_R', 80.0), 10.0, 1, "像素")
        self.radial_max_cone_spin, _, w2 = self._spin_with_slider(60, 200, getattr(self.parent(), 'RADIAL_MAX_CONE', 120), "度")
        self.radial_pad_arc_spin, _, w3 = self._dspin_with_slider(2.0, 24.0, getattr(self.parent(), 'RADIAL_PAD_ARC', 6.0), 1.0, 1, "度")
        self.radial_stretch_step_spin, _, w4 = self._dspin_with_slider(10.0, 100.0, getattr(self.parent(), 'RADIAL_STRETCH_STEP', 40.0), 5.0, 1, "像素")
        f.addRow("基础半径:", w1)
        f.addRow("最大锥角:", w2)
        f.addRow("弧填充:", w3)
        f.addRow("拉伸步长:", w4)
        lay.addWidget(g); lay.addStretch(1)
        return tab

    def _make_tab_view(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g = self._group("对齐参数")
        f = QFormLayout(g)
        self.snap_step_spin, _, w1 = self._spin_with_slider(10, 80, getattr(self.parent(), 'SNAP_STEP', 40), "像素")
        self.align_threshold_spin, _, w2 = self._spin_with_slider(4, 24, getattr(self.parent(), 'ALIGN_THRESHOLD', 8), "像素")
        f.addRow("对齐步长:", w1)
        f.addRow("对齐阈值:", w2)
        lay.addWidget(g); lay.addStretch(1)
        return tab

    def _make_tab_performance(self) -> QWidget:
        tab = QWidget(); lay = QVBoxLayout(tab); lay.setSpacing(16); lay.setContentsMargins(20, 20, 20, 20)
        g = self._group("性能参数")
        f = QFormLayout(g)
        self.history_limit_spin, _, w1 = self._spin_with_slider(10, 500, getattr(self.parent(), 'HISTORY_LIMIT', 100))
        self.autosave_delay_spin, _, w2 = self._spin_with_slider(100, 5000, getattr(self.parent(), 'AUTOSAVE_DELAY', 300), "毫秒")
        f.addRow("历史记录限制:", w1)
        f.addRow("自动保存延迟:", w2)
        lay.addWidget(g); lay.addStretch(1)
        return tab

    # ---------------- 值收集 ----------------
    def get_values(self) -> Dict[str, float]:
        return {
            # 布局
            'TARGET_EDGE': self.target_edge_spin.value(),
            'MIN_CHORD_RATIO': self.min_chord_ratio_spin.value(),
            'MAX_EXTRA_STRETCH': self.max_extra_stretch_spin.value(),
            'EDGE_LENGTH_FACTOR': self.edge_length_factor_spin.value(),
            'SPATIAL_HASH_CELL_SIZE': self.spatial_hash_cell_spin.value(),
            'MIN_NODE_DISTANCE': self.min_node_distance_spin.value(),
            # 节点
            'NODE_FONT_SIZE': self.node_font_size_spin.value(),
            'NODE_PADDING_X': self.node_padding_x_spin.value(),
            'NODE_PADDING_Y': self.node_padding_y_spin.value(),
            'NODE_CORNER_RADIUS': self.node_corner_radius_spin.value(),
            # 边
            'EDGE_BASE_RADIUS': self.edge_base_radius_spin.value(),
            'EDGE_RING_SPACING': self.edge_ring_spacing_spin.value(),
            'EDGE_CONTROL_POINT_RATIO': self.edge_control_point_ratio_spin.value(),
            'EDGE_BEND_RATIO': self.edge_bend_ratio_spin.value(),
            # 排列
            'RADIAL_BASE_R': self.radial_base_r_spin.value(),
            'RADIAL_MAX_CONE': self.radial_max_cone_spin.value(),
            'RADIAL_PAD_ARC': self.radial_pad_arc_spin.value(),
            'RADIAL_STRETCH_STEP': self.radial_stretch_step_spin.value(),
            # 视图
            'SNAP_STEP': self.snap_step_spin.value(),
            'ALIGN_THRESHOLD': self.align_threshold_spin.value(),
            # 性能
            'HISTORY_LIMIT': self.history_limit_spin.value(),
            'AUTOSAVE_DELAY': self.autosave_delay_spin.value(),
        }

    def get_creational_values(self) -> Dict[str, float]:
        return {
            'NODE_FONT_SIZE': self.node_font_size_spin.value(),
            'NODE_PADDING_X': self.node_padding_x_spin.value(),
            'NODE_PADDING_Y': self.node_padding_y_spin.value(),
            'NODE_CORNER_RADIUS': self.node_corner_radius_spin.value(),
        }

    # ---------------- 动作 ----------------
    def apply_current_values(self):
        self.defaults_applied.emit(self.get_creational_values())
        if self.apply_existing_chk.isChecked():
            self.apply_to_existing.emit(self.get_values())

    def restore_current_tab_defaults(self):
        # 与原版保持相同默认
        d = {
            'TARGET_EDGE': 180, 'MIN_CHORD_RATIO': 0.8, 'MAX_EXTRA_STRETCH': 3.0,
            'EDGE_LENGTH_FACTOR': 1.0, 'SPATIAL_HASH_CELL_SIZE': 120, 'MIN_NODE_DISTANCE': 140,
            'NODE_FONT_SIZE': 12, 'NODE_PADDING_X': 8, 'NODE_PADDING_Y': 6, 'NODE_CORNER_RADIUS': 12,
            'EDGE_BASE_RADIUS': 160.0, 'EDGE_RING_SPACING': 160.0, 'EDGE_CONTROL_POINT_RATIO': 0.15, 'EDGE_BEND_RATIO': 0.05,
            'RADIAL_BASE_R': 80.0, 'RADIAL_MAX_CONE': 120, 'RADIAL_PAD_ARC': 6.0, 'RADIAL_STRETCH_STEP': 40.0,
            'SNAP_STEP': 40, 'ALIGN_THRESHOLD': 8,
            'HISTORY_LIMIT': 100, 'AUTOSAVE_DELAY': 300,
        }
        i = self.tab_widget.currentIndex()
        if i == 0:
            self.target_edge_spin.setValue(d['TARGET_EDGE'])
            self.min_chord_ratio_spin.setValue(d['MIN_CHORD_RATIO'])
            self.max_extra_stretch_spin.setValue(d['MAX_EXTRA_STRETCH'])
            self.edge_length_factor_spin.setValue(d['EDGE_LENGTH_FACTOR'])
            self.spatial_hash_cell_spin.setValue(d['SPATIAL_HASH_CELL_SIZE'])
            self.min_node_distance_spin.setValue(d['MIN_NODE_DISTANCE'])
        elif i == 1:
            self.node_font_size_spin.setValue(d['NODE_FONT_SIZE'])
            self.node_padding_x_spin.setValue(d['NODE_PADDING_X'])
            self.node_padding_y_spin.setValue(d['NODE_PADDING_Y'])
            self.node_corner_radius_spin.setValue(d['NODE_CORNER_RADIUS'])
        elif i == 2:
            self.edge_base_radius_spin.setValue(d['EDGE_BASE_RADIUS'])
            self.edge_ring_spacing_spin.setValue(d['EDGE_RING_SPACING'])
            self.edge_control_point_ratio_spin.setValue(d['EDGE_CONTROL_POINT_RATIO'])
            self.edge_bend_ratio_spin.setValue(d['EDGE_BEND_RATIO'])
        elif i == 3:
            self.radial_base_r_spin.setValue(d['RADIAL_BASE_R'])
            self.radial_max_cone_spin.setValue(d['RADIAL_MAX_CONE'])
            self.radial_pad_arc_spin.setValue(d['RADIAL_PAD_ARC'])
            self.radial_stretch_step_spin.setValue(d['RADIAL_STRETCH_STEP'])
        elif i == 4:
            self.snap_step_spin.setValue(d['SNAP_STEP'])
            self.align_threshold_spin.setValue(d['ALIGN_THRESHOLD'])
        elif i == 5:
            self.history_limit_spin.setValue(d['HISTORY_LIMIT'])
            self.autosave_delay_spin.setValue(d['AUTOSAVE_DELAY'])
        self._on_any_value_changed()

    def restore_defaults(self):
        # 全部恢复默认
        spec = {
            'TARGET_EDGE': (self.target_edge_spin, 180),
            'MIN_CHORD_RATIO': (self.min_chord_ratio_spin, 0.8),
            'MAX_EXTRA_STRETCH': (self.max_extra_stretch_spin, 3.0),
            'EDGE_LENGTH_FACTOR': (self.edge_length_factor_spin, 1.0),
            'SPATIAL_HASH_CELL_SIZE': (self.spatial_hash_cell_spin, 120),
            'MIN_NODE_DISTANCE': (self.min_node_distance_spin, 140),
            'NODE_FONT_SIZE': (self.node_font_size_spin, 12),
            'NODE_PADDING_X': (self.node_padding_x_spin, 8),
            'NODE_PADDING_Y': (self.node_padding_y_spin, 6),
            'NODE_CORNER_RADIUS': (self.node_corner_radius_spin, 12),
            'EDGE_BASE_RADIUS': (self.edge_base_radius_spin, 160.0),
            'EDGE_RING_SPACING': (self.edge_ring_spacing_spin, 160.0),
            'EDGE_CONTROL_POINT_RATIO': (self.edge_control_point_ratio_spin, 0.15),
            'EDGE_BEND_RATIO': (self.edge_bend_ratio_spin, 0.05),
            'RADIAL_BASE_R': (self.radial_base_r_spin, 80.0),
            'RADIAL_MAX_CONE': (self.radial_max_cone_spin, 120),
            'RADIAL_PAD_ARC': (self.radial_pad_arc_spin, 6.0),
            'RADIAL_STRETCH_STEP': (self.radial_stretch_step_spin, 40.0),
            'SNAP_STEP': (self.snap_step_spin, 40),
            'ALIGN_THRESHOLD': (self.align_threshold_spin, 8),
            'HISTORY_LIMIT': (self.history_limit_spin, 100),
            'AUTOSAVE_DELAY': (self.autosave_delay_spin, 300),
        }
        for w, v in spec.values():
            w.setValue(v)
        self._on_any_value_changed()

    # ---------------- 搜索 & 导入导出 ----------------
    def _on_search(self, text: str):
        t = (text or "").strip()
        if not t:
            for g in self._groups:
                g.setVisible(True)
            return
        t = t.lower()
        for g in self._groups:
            title = g.title().lower()
            # 若组标题匹配，整组显示；否则看表单里的标签
            show = t in title
            if not show:
                lay = g.layout()
                # 遍历 QFormLayout 的 labelItem
                for i in range(lay.rowCount()):
                    li = lay.itemAt(i, QFormLayout.LabelRole)
                    if li and li.widget():
                        if t in li.widget().text().lower():
                            show = True; break
            g.setVisible(show)

    def _export_json(self):
        fn, _ = QFileDialog.getSaveFileName(self, "导出设置为 JSON", str(Path.home() / "mindmap_settings.json"), "JSON (*.json)")
        if not fn:
            return
        try:
            with open(fn, 'w', encoding='utf-8') as f:
                json.dump(self.get_values(), f, ensure_ascii=False, indent=2)
            QMessageBox.information(self, "成功", "设置已导出为 JSON。")
        except Exception as e:
            QMessageBox.critical(self, "失败", f"导出失败: {e}")

    def _import_json(self):
        fn, _ = QFileDialog.getOpenFileName(self, "导入设置（JSON）", str(Path.home()), "JSON (*.json)")
        if not fn:
            return
        try:
            with open(fn, 'r', encoding='utf-8') as f:
                data = json.load(f)
            # 仅对存在键的控件赋值
            m = {
                'TARGET_EDGE': self.target_edge_spin,
                'MIN_CHORD_RATIO': self.min_chord_ratio_spin,
                'MAX_EXTRA_STRETCH': self.max_extra_stretch_spin,
                'EDGE_LENGTH_FACTOR': self.edge_length_factor_spin,
                'SPATIAL_HASH_CELL_SIZE': self.spatial_hash_cell_spin,
                'MIN_NODE_DISTANCE': self.min_node_distance_spin,
                'NODE_FONT_SIZE': self.node_font_size_spin,
                'NODE_PADDING_X': self.node_padding_x_spin,
                'NODE_PADDING_Y': self.node_padding_y_spin,
                'NODE_CORNER_RADIUS': self.node_corner_radius_spin,
                'EDGE_BASE_RADIUS': self.edge_base_radius_spin,
                'EDGE_RING_SPACING': self.edge_ring_spacing_spin,
                'EDGE_CONTROL_POINT_RATIO': self.edge_control_point_ratio_spin,
                'EDGE_BEND_RATIO': self.edge_bend_ratio_spin,
                'RADIAL_BASE_R': self.radial_base_r_spin,
                'RADIAL_MAX_CONE': self.radial_max_cone_spin,
                'RADIAL_PAD_ARC': self.radial_pad_arc_spin,
                'RADIAL_STRETCH_STEP': self.radial_stretch_step_spin,
                'SNAP_STEP': self.snap_step_spin,
                'ALIGN_THRESHOLD': self.align_threshold_spin,
                'HISTORY_LIMIT': self.history_limit_spin,
                'AUTOSAVE_DELAY': self.autosave_delay_spin,
            }
            for k, v in (data or {}).items():
                if k in m:
                    m[k].setValue(v)
            self._on_any_value_changed()
            QMessageBox.information(self, "成功", "设置已从 JSON 导入。")
        except Exception as e:
            QMessageBox.critical(self, "失败", f"导入失败: {e}")

    # ---------------- 即时预览 ----------------
    def _on_any_value_changed(self, *_):
        if not self.live_preview_toggle.isChecked():
            return
        # 收集更多参数用于预览
        params = {
            "NODE_FONT_SIZE": self.node_font_size_spin.value(),
            "NODE_PADDING_X": self.node_padding_x_spin.value(),
            "NODE_PADDING_Y": self.node_padding_y_spin.value(),
            "NODE_CORNER_RADIUS": self.node_corner_radius_spin.value(),
            "EDGE_LENGTH_FACTOR": self.edge_length_factor_spin.value(),
            "SNAP_STEP": self.snap_step_spin.value(),
            "EDGE_CONTROL_POINT_RATIO": self.edge_control_point_ratio_spin.value(),
            "EDGE_BEND_RATIO": self.edge_bend_ratio_spin.value(),
        }
        self.preview.setParameters(params)

    # ---------------- 样式 ----------------
    def _apply_modern_style(self):
        self.setStyleSheet(
            """
            SettingsDialog { background: qlineargradient(x1:0,y1:0,x2:1,y2:1, stop:0 #f8fafc, stop:1 #e2e8f0); }
            QTabWidget::pane { border:1px solid #cbd5e0; border-radius:8px; background:white; margin-top:6px; }
            QTabBar::tab { background:#e2e8f0; border:1px solid #cbd5e0; border-bottom:none; border-top-left-radius:6px; border-top-right-radius:6px; padding:10px 16px; margin-right:4px; color:#4a5568; font-weight:600; }
            QTabBar::tab:selected { background:white; color:#2d3748; }
            QGroupBox { font-weight:600; font-size:14px; color:#2d3748; border:1px solid #e2e8f0; border-radius:8px; margin-top:16px; padding-top:12px; background:white; }
            QGroupBox::title { subcontrol-origin: margin; left: 12px; padding:0 8px; background:qlineargradient(x1:0,y1:0,x2:1,y2:0, stop:0 #4fd1c7, stop:1 #4299e1); color:white; border-radius:4px; }
            QLabel { color:#4a5568; font-weight:500; padding:4px 0; }
            QSpinBox, QDoubleSpinBox, QLineEdit { padding:8px 10px; border:1px solid #cbd5e0; border-radius:6px; background:white; font-size:14px; min-width: 90px; }
            QSpinBox:focus, QDoubleSpinBox:focus, QLineEdit:focus { border-color:#4299e1; }
            QSlider::groove:horizontal { height:6px; background:#e2e8f0; border-radius:3px; }
            QSlider::handle:horizontal { width:16px; margin:-6px 0; border-radius:8px; background:#4299e1; }
            QPushButton { padding:10px 20px; border:none; border-radius:6px; font-weight:700; }
            QPushButton:hover { border: 1px solid #4299e1; }
            QToolButton { padding:8px 12px; border:1px solid #cbd5e0; border-radius:6px; background:#edf2f7; }
            QToolButton:hover { border: 1px solid #4299e1; }
            """
        )


# -------------------------- 小工具函数 --------------------------
def qcolor_to_hex(c: QColor) -> str:
    return "#{:02X}{:02X}{:02X}".format(c.red(), c.green(), c.blue())

def hex_to_qcolor(s: str) -> QColor:
    qc = QColor(s)
    return qc if qc.isValid() else QColor(173, 216, 230)

def center_in_scene(item: QGraphicsItem) -> QPointF:
    return item.mapToScene(item.boundingRect().center())

def _angle_normalize(a: float) -> float:
    twopi = 2.0 * math.pi
    a = a % twopi
    if a < 0:
        a += twopi
    return a

def _angle_between(p_center: QPointF, p: QPointF) -> float:
    return _angle_normalize(math.atan2(p.y() - p_center.y(), p.x() - p_center.x()))

def vsep() -> QWidget:
    line = QFrame(); line.setFrameShape(QFrame.VLine); line.setFrameShadow(QFrame.Sunken); line.setStyleSheet("color:#cbd5e0")
    return line

# ---------------------------- 视图 ----------------------------
class MindMapView(QGraphicsView):
    def __init__(self, scene, parent=None):
        super().__init__(scene, parent)
        self.setRenderHint(QPainter.Antialiasing)
        self.setDragMode(QGraphicsView.RubberBandDrag)
        self.setTransformationAnchor(QGraphicsView.AnchorUnderMouse)
        self.setResizeAnchor(QGraphicsView.AnchorViewCenter)
        self.setViewportUpdateMode(QGraphicsView.BoundingRectViewportUpdate)

        # 平移状态
        self._panning = False
        self._last_pan_point = None

        # 右键长按平移相关
        self._right_is_down = False
        self._right_down_pos = None
        self._right_long_pan = False
        self._right_press_timer = QTimer(self)
        self._right_press_timer.setSingleShot(True)
        self._right_press_timer.timeout.connect(self._on_right_long_press)

        # 可选：按住空格也允许临时平移
        self._space_pan = False
        self._pan_mode = False

    def wheelEvent(self, event):
        zoom_in_factor = 1.15
        zoom_out_factor = 1.0 / zoom_in_factor
        factor = zoom_in_factor if event.angleDelta().y() > 0 else zoom_out_factor
        new = QTransform(self.transform())
        new.scale(factor, factor)
        if 0.1 <= new.m11() <= 4.0:
            self.setTransform(new)

    def _begin_pan(self, pos):
        self._panning = True
        self._last_pan_point = pos
        self.setCursor(Qt.ClosedHandCursor)

    def _do_pan(self, pos):
        delta = pos - self._last_pan_point
        self._last_pan_point = pos
        self.horizontalScrollBar().setValue(self.horizontalScrollBar().value() - delta.x())
        self.verticalScrollBar().setValue(self.verticalScrollBar().value() - delta.y())

    def _end_pan(self):
        self._panning = False
        if self._space_pan or self._pan_mode:
            self.setCursor(Qt.OpenHandCursor)
        else:
            self.setCursor(Qt.ArrowCursor)

    def mousePressEvent(self, event):
        if (event.button() == Qt.LeftButton and (self._pan_mode or self._space_pan)) or event.button() == Qt.MiddleButton:
            self._begin_pan(event.pos())
            event.accept()
            return

        if event.button() == Qt.RightButton:
            self._right_is_down = True
            self._right_down_pos = event.pos()
            self._right_long_pan = False
            self._right_press_timer.start(220)
            event.accept()
            return

        super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        if self._right_is_down and not self._panning:
            if (event.pos() - self._right_down_pos).manhattanLength() > 6:
                self._right_press_timer.stop()
                self._right_long_pan = True
                self._begin_pan(self._right_down_pos)
                event.accept()
                return

        if self._panning:
            self._do_pan(event.pos())
            event.accept()
            return

        super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        if event.button() == Qt.RightButton:
            self._right_press_timer.stop()
            if self._panning or self._right_long_pan:
                self._end_pan()
                self._right_is_down = False
                self._right_long_pan = False
                event.accept()
                return
            self._right_is_down = False
            self._right_long_pan = False
            super().mouseReleaseEvent(event)
            return

        if self._panning and (event.button() in (Qt.LeftButton, Qt.MiddleButton)):
            self._end_pan()
            event.accept()
            return

        super().mouseReleaseEvent(event)

    def contextMenuEvent(self, event):
        if self._right_long_pan or self._panning:
            event.accept()
            return
        super().contextMenuEvent(event)

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Space and not self._space_pan:
            self._space_pan = True
            self.setCursor(Qt.OpenHandCursor)
        super().keyPressEvent(event)

    def keyReleaseEvent(self, event):
        if event.key() == Qt.Key_Space and self._space_pan:
            self._space_pan = False
            self.setCursor(Qt.OpenHandCursor if self._pan_mode else Qt.ArrowCursor)
        super().keyReleaseEvent(event)

    def _on_right_long_press(self):
        if self._right_is_down and not self._panning:
            self._right_long_pan = True
            self._begin_pan(self._right_down_pos)

    def set_pan_mode(self, enabled: bool):
        self._pan_mode = bool(enabled)
        self.setCursor(Qt.OpenHandCursor if enabled else Qt.ArrowCursor)

# ---------------------------- 边 ----------------------------
class MindMapEdge(QGraphicsPathItem):
    def __init__(self, node1, node2, color=QColor(120, 120, 120)):
        super().__init__()
        self.node_pair = (node1, node2)
        self._pen = QPen(color, 2)
        self._pen.setCosmetic(True)
        self.setPen(self._pen)
        self.setZValue(-1)
        self.update_path()

    def update_path(self):
        n1, n2 = self.node_pair
        p1 = center_in_scene(n1)
        p2 = center_in_scene(n2)
        path = QPainterPath(p1)

        dx = p2.x() - p1.x()
        dy = p2.y() - p1.y()
        d = math.hypot(dx, dy) or 1.0
        ux, uy = dx / d, dy / d
        nx_, ny_ = -uy, ux

        # 安全地获取参数
        edge_length_factor = 1.0
        scene = self.scene()
        if scene and hasattr(scene, 'parent') and scene.parent:
            parent_app = scene.parent
            edge_length_factor = getattr(parent_app, 'EDGE_LENGTH_FACTOR', 1.0)
            
            # 计算节点层级
            try:
                level1 = parent_app._get_node_level(n1.name)
                level2 = parent_app._get_node_level(n2.name)
                
                # 确定父子关系（层级较低的为父节点）
                parent_node = n1 if level1 < level2 else n2
                child_node = n2 if level1 < level2 else n1
                
                # 基于父节点和子节点的相对位置决定弯曲方向
                parent_pos = parent_node.pos()
                child_pos = child_node.pos()
                
                # 计算相对于父节点的角度
                rel_angle = math.atan2(child_pos.y() - parent_pos.y(), 
                                    child_pos.x() - parent_pos.x())
                
                # 将角度映射到 [0, 2π) 范围
                if rel_angle < 0:
                    rel_angle += 2 * math.pi
                    
                # 根据层级和角度决定弯曲方向
                base_level = min(level1, level2)
                sector = int(rel_angle / (math.pi / 4)) % 8
                
                # 奇数层级：右半圆向上弯曲，左半圆向下弯曲
                # 偶数层级：右半圆向下弯曲，左半圆向上弯曲
                if base_level % 2 == 1:  # 奇数层级
                    if sector < 4:  # 右半圆
                        sign = 1  # 向上
                    else:  # 左半圆
                        sign = -1  # 向下
                else:  # 偶数层级
                    if sector < 4:  # 右半圆
                        sign = -1  # 向下
                    else:  # 左半圆
                        sign = 1  # 向上
            except (AttributeError, KeyError, TypeError) as e:
                # 只捕获预期的异常，其他异常继续抛出
                logger.debug(f"边弯曲方向计算失败，使用备用方案: {e}")
                # 备用方案：基于节点名称哈希
                sign = 1 if (hash(n1.name) + hash(n2.name)) % 2 == 0 else -1
            except Exception as e:
                # 其他异常记录并重新抛出
                logger.error(f"边弯曲方向计算出现意外错误: {e}")
                raise
        else:
            # 备用方案：基于节点名称哈希
            sign = 1 if (hash(n1.name) + hash(n2.name)) % 2 == 0 else -1

        # 使用动态连线长度系数
        t = d * 0.15 * edge_length_factor
        b = min(30.0, d * 0.05 * edge_length_factor)

        # 对于非常近的节点，减小弯曲幅度
        if d < 100:
            b = d * 0.03 * edge_length_factor

        c1 = QPointF(p1.x() + ux * t + nx_ * b * sign, p1.y() + uy * t + ny_ * b * sign)
        c2 = QPointF(p2.x() - ux * t + nx_ * b * sign, p2.y() - uy * t + ny_ * b * sign)

        path.cubicTo(c1, c2, p2)
        self.setPath(path)

    def set_color(self, color: QColor):
        self._pen.setColor(color)
        self.setPen(self._pen)

# ---------------------------- 节点 ----------------------------
class MindMapNode(QGraphicsObject):
    moved = pyqtSignal(object)
    color_changed = pyqtSignal(object)
    renamed = pyqtSignal(object, str, str)

    def __init__(self, name, color: QColor = QColor(173, 216, 230), *, font_size:int=12, pad_x:int=8, pad_y:int=6, corner_radius:int=12):
        QGraphicsObject.__init__(self)
        self.name = name
        self.color = color
        self._font_size = int(font_size)
        self._pad_x = int(pad_x)
        self._pad_y = int(pad_y)
        self._corner_radius = int(corner_radius)

        self.setFlag(QGraphicsItem.ItemIsMovable, True)
        self.setFlag(QGraphicsItem.ItemIsSelectable, True)
        self.setFlag(QGraphicsItem.ItemSendsGeometryChanges, True)
        self.setCacheMode(QGraphicsItem.DeviceCoordinateCache)
        self.setAcceptHoverEvents(True)

        self.text_item = QGraphicsTextItem(name, self)
        self.text_item.setDefaultTextColor(Qt.black)
        # 增大字体大小
        self.text_item.setFont(QFont("Segoe UI", self._font_size, QFont.Medium))
        self.text_item.setFlag(QGraphicsItem.ItemIsSelectable, False)

        self._hover = False

        self._recenter_text()
        self._update_rect()

        self.base_pen = QPen(QColor(30, 70, 120), 2)
        self.base_pen.setCosmetic(True)
        self.highlight_pen = QPen(QColor(20, 20, 20), 3)
        self.highlight_pen.setCosmetic(True)

        self.setAcceptedMouseButtons(Qt.LeftButton | Qt.RightButton)

    def _recenter_text(self):
        tr = self.text_item.boundingRect()
        self.text_item.setPos(-tr.width() / 2, -tr.height() / 2)

    def _update_rect(self):
        tr = self.text_item.boundingRect()
        pad_x, pad_y = self._pad_x, self._pad_y
        self.rect = QRectF(-tr.width() / 2 - pad_x, -tr.height() / 2 - pad_y,
                           tr.width() + 2 * pad_x, tr.height() + 2 * pad_y)

    def boundingRect(self):
        return self.rect.adjusted(-6, -6, 6, 6)

    def shape(self):
        path = QPainterPath()
        r = self.rect.adjusted(-2, -2, 2, 2)
        path.addRoundedRect(r, self._corner_radius, self._corner_radius)
        return path

    def paint(self, painter, option, widget):
        shadow_rect = self.rect.translated(2, 3)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor(0, 0, 0, 35))
        painter.drawRoundedRect(shadow_rect, self._corner_radius, self._corner_radius)

        grad = QLinearGradient(self.rect.topLeft(), self.rect.bottomRight())
        base = QColor(self.color)
        lighter = QColor(base).lighter(135)
        darker = QColor(base).darker(115)
        grad.setColorAt(0.0, lighter)
        grad.setColorAt(1.0, darker)

        painter.setBrush(QBrush(grad))
        painter.setPen(self.highlight_pen if (self._hover or self.isSelected()) else self.base_pen)
        painter.drawRoundedRect(self.rect, self._corner_radius, self._corner_radius)

    def set_color(self, color: QColor):
        self.color = QColor(color)
        self.update()
        self.color_changed.emit(self)

    def set_name(self, new_name: str):
        old_name = self.name
        self.name = new_name
        self.text_item.setPlainText(new_name)
        self._recenter_text()
        self._update_rect()
        self.update()
        self.renamed.emit(self, old_name, new_name)

    def mousePressEvent(self, event):
        if event.button() == Qt.LeftButton:
            scene = self.scene()
            if scene and hasattr(scene, 'parent'):
                # 清除其他节点的选择状态，实现单选
                for item in scene.items():
                    if isinstance(item, MindMapNode) and item != self:
                        item.setSelected(False)
                scene.parent.select_node(self)
        super().mousePressEvent(event)

    def itemChange(self, change, value):
        parent = None
        scene = self.scene()
        if scene and hasattr(scene, 'parent'):
            parent = scene.parent
        if change == QGraphicsItem.ItemPositionChange and parent is not None:
            step = parent.snap_step
            p = value
            if isinstance(p, QPointF):
                snapped = QPointF(round(p.x() / step) * step, round(p.y() / step) * step)
                return snapped
        if change == QGraphicsItem.ItemPositionHasChanged:
            self.moved.emit(self)
            if scene and parent is not None and parent.graph is not None and parent.graph.has_node(self.name):
                parent.graph.nodes[self.name]['pos'] = (self.x(), self.y())
        return super().itemChange(change, value)

    def contextMenuEvent(self, event):
        menu = QMenu()
        act_rename = menu.addAction("重命名节点")

        sub = menu.addMenu("更改颜色")
        palette = [
            ("湖蓝", QColor("#7EC8E3")),
            ("薄荷绿", QColor("#8EE3C2")),
            ("向日黄", QColor("#FFD166")),
            ("珊瑚橙", QColor("#FF9F80")),
            ("薰衣草", QColor("#C6B3FF")),
            ("玫瑰粉", QColor("#F7A8B8")),
            ("苹果绿", QColor("#9AD576")),
            ("天空蓝", QColor("#9AD0F5")),
        ]
        color_actions = []
        for name, c in palette:
            act = sub.addAction(name)
            act.setData(c)
            color_actions.append(act)
        sub.addSeparator()
        act_custom = sub.addAction("自定义")
        act_delete = menu.addAction("删除节点 (Ctrl+D)")
        chosen = menu.exec_(event.screenPos())

        if chosen == act_rename:
            self.rename_node()
        elif chosen in color_actions:
            self.set_color(chosen.data())
        elif chosen == act_custom:
            c = QColorDialog.getColor(self.color, None, "选择颜色")
            if c.isValid():
                self.set_color(c)
        elif chosen == act_delete:
            scene = self.scene()
            if scene and hasattr(scene, 'parent'):
                scene.parent.delete_specific_node(self)

    def rename_node(self):
        new_name, ok = QInputDialog.getText(
            None, "重命名节点", "输入新名称:", text=self.name
        )
        if ok and new_name and new_name != self.name:
            scene = self.scene()
            if scene and hasattr(scene, 'parent'):
                parent = scene.parent
                # 生成不冲突的新名称，然后直接调用 set_name，让信号正常发出
                unique_name = parent._ensure_unique_name(new_name, exclude=self.name)
                self.set_name(unique_name)

    def hoverEnterEvent(self, event):
        self._hover = True
        self.update()
        super().hoverEnterEvent(event)

    def hoverLeaveEvent(self, event):
        self._hover = False
        self.update()
        super().hoverLeaveEvent(event)

# ---------------------------- 场景 ----------------------------
class MindMapScene(QGraphicsScene):
    selection_changed = pyqtSignal()

    def __init__(self, parent=None):
        super().__init__(parent)
        self.parent = parent
        self.edges_by_node = defaultdict(set)
        self._guide_h = None
        self._guide_v = None
        self.selectionChanged.connect(self._on_selection_changed)

    def _on_selection_changed(self):
        """确保单选模式：如果选择了多个项目，只保留最后一个"""
        selected_items = self.selectedItems()
        if len(selected_items) > 1:
            # 只保留最后一个选择的项目
            for item in selected_items[:-1]:
                item.setSelected(False)
        self.selection_changed.emit()

    def add_connection(self, edge_item: MindMapEdge, node1: MindMapNode, node2: MindMapNode):
        edge_item.node_pair = (node1, node2)
        self.edges_by_node[node1].add(edge_item)
        self.edges_by_node[node2].add(edge_item)

    def remove_connection(self, edge_item: MindMapEdge):
        if not hasattr(edge_item, 'node_pair'):
            return
        n1, n2 = edge_item.node_pair
        self.edges_by_node[n1].discard(edge_item)
        self.edges_by_node[n2].discard(edge_item)

    def update_connections_for(self, moved_node: MindMapNode):
        for edge in list(self.edges_by_node[moved_node]):
            edge.update_path()

    def drawBackground(self, painter, rect):
        painter.save()
        painter.setRenderHint(QPainter.Antialiasing, False)
        painter.fillRect(rect, QColor(248, 250, 253))
        step = 40
        light = QColor(225, 232, 245)
        painter.setPen(QPen(light, 0))
        x0 = int(rect.left()) - (int(rect.left()) % step)
        y0 = int(rect.top()) - (int(rect.top()) % step)
        for x in range(x0, int(rect.right()) + step, step):
            painter.drawLine(QPointF(x, rect.top()), QPointF(x, rect.bottom()))
        for y in range(y0, int(rect.bottom()) + step, step):
            painter.drawLine(QPointF(rect.left(), y), QPointF(rect.right(), y))
        painter.restore()

    def show_guides(self, x=None, y=None):
        br = self.itemsBoundingRect().adjusted(-200, -200, 200, 200)
        pen = QPen(QColor(230, 80, 80, 160), 1, Qt.DashLine)
        pen.setCosmetic(True)
        if x is not None:
            if self._guide_v is None:
                from PyQt5.QtWidgets import QGraphicsLineItem
                self._guide_v = self.addLine(0, 0, 0, 0, pen)
                self._guide_v.setZValue(1000)
            self._guide_v.setPen(pen)
            self._guide_v.setLine(x, br.top(), x, br.bottom())
            self._guide_v.show()
        else:
            if self._guide_v is not None:
                self._guide_v.hide()
        if y is not None:
            if self._guide_h is None:
                from PyQt5.QtWidgets import QGraphicsLineItem
                self._guide_h = self.addLine(0, 0, 0, 0, pen)
                self._guide_h.setZValue(1000)
            self._guide_h.setPen(pen)
            self._guide_h.setLine(br.left(), y, br.right(), y)
            self._guide_h.show()
        else:
            if self._guide_h is not None:
                self._guide_h.hide()

    def clear_guides(self):
        if self._guide_h:
            self._guide_h.hide()
        if self._guide_v:
            self._guide_v.hide()

# ---------------------------- 主窗体 ----------------------------
class MindMapApp(QMainWindow):
    CONFIG_PATH = str(Path.home() / ".mindmap_ui_state.json")

    def __init__(self):
        super().__init__()
        self.setWindowTitle("思维导图 - 优化版 (名称唯一标识)")
        
        # 加载设置
        self.load_all_settings()
        
        # 初始化运行期默认值（以当前全局参数为基）
        self._runtime_defaults = {
            'NODE_FONT_SIZE': getattr(self, 'NODE_FONT_SIZE', 12),
            'NODE_PADDING_X': getattr(self, 'NODE_PADDING_X', 8),
            'NODE_PADDING_Y': getattr(self, 'NODE_PADDING_Y', 6),
            'NODE_CORNER_RADIUS': getattr(self, 'NODE_CORNER_RADIUS', 12),
        }
        
        try:
            ag = QGuiApplication.primaryScreen().availableGeometry()
            w = int(ag.width() * 0.8)
            h = int(ag.height() * 0.8)
            x = ag.x() + (ag.width() - w) // 2
            y = ag.y() + (ag.height() - h) // 2
            self.setGeometry(x, y, w, h)
        except Exception as e:
            logger.warning(f"无法获取屏幕几何信息，使用默认尺寸: {e}")
            self.setGeometry(60, 60, 1400, 900)

        self.graph = nx.Graph()
        self.nodes = {}  # 名称 -> MindMapNode

        # 初始化节点层级缓存
        self._node_level_cache = {}

        # 空间哈希用于近邻加速与碰撞检测 - 在加载设置后初始化
        cell_size = self.SPATIAL_HASH_CELL_SIZE
        self._spatial = _SpatialHash(cell=cell_size)
        self._pos_cache = {}
        self.edges = []
        self.selected_node = None
        self.last_anchor_name = None
        self.root_node_name = None

        self.snap_step = self.SNAP_STEP
        self.align_threshold = self.ALIGN_THRESHOLD

        self.undo_stack = []
        self.redo_stack = []
        self._history_timer = QTimer(self)
        self._history_timer.setSingleShot(True)
        self._history_timer.timeout.connect(lambda: self.push_history("move"))
        self._autosave_timer = QTimer(self)
        self._autosave_timer.setSingleShot(True)
        self._autosave_timer.timeout.connect(self.autosave)

        self.scene = MindMapScene(self)
        self.scene.selection_changed.connect(self.on_scene_selection_changed)
        self.view = MindMapView(self.scene, self)

        central = QWidget()
        self.setCentralWidget(central)
        main_layout = QHBoxLayout(central)

        main_layout.addWidget(self.create_left_sidebar())
        main_layout.addWidget(self.view, stretch=1)
        main_layout.addWidget(self.create_right_panel())

        QShortcut(QKeySequence("Ctrl+D"), self, self.delete_node)
        QShortcut(QKeySequence("Ctrl+S"), self, self.autosave)
        QShortcut(QKeySequence("Ctrl+O"), self, self.import_map)
        QShortcut(QKeySequence("Ctrl+Z"), self, self.undo)
        QShortcut(QKeySequence("Ctrl+Y"), self, self.redo)
        QShortcut(QKeySequence("N"), self, self.add_node_smart_from_selection)

        self._apply_stylesheet()

        self._palette_cycle = [
            QColor("#7EC8E3"), QColor("#8EE3C2"), QColor("#FFD166"),
            QColor("#FF9F80"), QColor("#C6B3FF"), QColor("#F7A8B8"),
            QColor("#9AD576"), QColor("#9AD0F5")
        ]
        self._next_color_idx = 0

        self.refresh_node_list()
        self.push_history("init")
        self._syncing_scene_to_list = False
        self._syncing_list_to_scene = False

        self.outline_window = None

        # 搜索防抖定时器
        self._search_timer = QTimer(self)
        self._search_timer.setSingleShot(True)
        self._search_timer.timeout.connect(self.refresh_node_list)

        # 启动后自动生成首个节点
        QTimer.singleShot(0, lambda: (self._ensure_root_node_exists(), self.push_history("auto_seed_init")))

        logger.info("思维导图应用初始化完成")

    def load_all_settings(self):
        """加载所有用户设置"""
        try:
            if Path(SETTINGS_PATH).exists():
                with open(SETTINGS_PATH, 'r', encoding='utf-8') as f:
                    settings = json.load(f)
                
                # 布局参数
                self.TARGET_EDGE = settings.get('TARGET_EDGE', 180)
                self.MIN_CHORD_RATIO = settings.get('MIN_CHORD_RATIO', 0.8)
                self.MAX_EXTRA_STRETCH = settings.get('MAX_EXTRA_STRETCH', 3.0)
                self.EDGE_LENGTH_FACTOR = settings.get('EDGE_LENGTH_FACTOR', 1.0)
                self.SPATIAL_HASH_CELL_SIZE = settings.get('SPATIAL_HASH_CELL_SIZE', 120)
                self.MIN_NODE_DISTANCE = settings.get('MIN_NODE_DISTANCE', 140)
                
                # 节点参数
                self.NODE_FONT_SIZE = settings.get('NODE_FONT_SIZE', 12)
                self.NODE_PADDING_X = settings.get('NODE_PADDING_X', 8)
                self.NODE_PADDING_Y = settings.get('NODE_PADDING_Y', 6)
                self.NODE_CORNER_RADIUS = settings.get('NODE_CORNER_RADIUS', 12)
                
                # 边参数
                self.EDGE_BASE_RADIUS = settings.get('EDGE_BASE_RADIUS', 160.0)
                self.EDGE_RING_SPACING = settings.get('EDGE_RING_SPACING', 160.0)
                self.EDGE_CONTROL_POINT_RATIO = settings.get('EDGE_CONTROL_POINT_RATIO', 0.15)
                self.EDGE_BEND_RATIO = settings.get('EDGE_BEND_RATIO', 0.05)
                
                # 排列算法参数
                self.RADIAL_BASE_R = settings.get('RADIAL_BASE_R', 80.0)
                self.RADIAL_MAX_CONE = settings.get('RADIAL_MAX_CONE', 120)
                self.RADIAL_PAD_ARC = settings.get('RADIAL_PAD_ARC', 6.0)
                self.RADIAL_STRETCH_STEP = settings.get('RADIAL_STRETCH_STEP', 40.0)
                
                # 视图参数
                self.SNAP_STEP = settings.get('SNAP_STEP', 40)
                self.ALIGN_THRESHOLD = settings.get('ALIGN_THRESHOLD', 8)
                
                # 性能参数
                self.HISTORY_LIMIT = settings.get('HISTORY_LIMIT', 100)
                self.AUTOSAVE_DELAY = settings.get('AUTOSAVE_DELAY', 300)
                
            else:
                # 使用默认值
                self.set_default_settings()
                
        except Exception as e:
            logger.error(f"加载设置失败: {e}")
            self.set_default_settings()
            
        # 更新自动保存定时器
        if hasattr(self, '_autosave_timer'):
            self._autosave_timer.setInterval(self.AUTOSAVE_DELAY)

    def set_default_settings(self):
        """设置所有参数的默认值"""
        # 布局参数
        self.TARGET_EDGE = 180
        self.MIN_CHORD_RATIO = 0.8
        self.MAX_EXTRA_STRETCH = 3.0
        self.EDGE_LENGTH_FACTOR = 1.0
        self.SPATIAL_HASH_CELL_SIZE = 120
        self.MIN_NODE_DISTANCE = 140
        
        # 节点参数
        self.NODE_FONT_SIZE = 12
        self.NODE_PADDING_X = 8
        self.NODE_PADDING_Y = 6
        self.NODE_CORNER_RADIUS = 12
        
        # 边参数
        self.EDGE_BASE_RADIUS = 160.0
        self.EDGE_RING_SPACING = 160.0
        self.EDGE_CONTROL_POINT_RATIO = 0.15
        self.EDGE_BEND_RATIO = 0.05
        
        # 排列算法参数
        self.RADIAL_BASE_R = 80.0
        self.RADIAL_MAX_CONE = 120
        self.RADIAL_PAD_ARC = 6.0
        self.RADIAL_STRETCH_STEP = 40.0
        
        # 视图参数
        self.SNAP_STEP = 40
        self.ALIGN_THRESHOLD = 8
        
        # 性能参数
        self.HISTORY_LIMIT = 100
        self.AUTOSAVE_DELAY = 300
        
    def save_all_settings(self):
        """保存所有用户设置"""
        try:
            settings = {
                # 布局参数
                'TARGET_EDGE': self.TARGET_EDGE,
                'MIN_CHORD_RATIO': self.MIN_CHORD_RATIO,
                'MAX_EXTRA_STRETCH': self.MAX_EXTRA_STRETCH,
                'EDGE_LENGTH_FACTOR': self.EDGE_LENGTH_FACTOR,
                'SPATIAL_HASH_CELL_SIZE': self.SPATIAL_HASH_CELL_SIZE,
                'MIN_NODE_DISTANCE': self.MIN_NODE_DISTANCE,
                
                # 节点参数
                'NODE_FONT_SIZE': self.NODE_FONT_SIZE,
                'NODE_PADDING_X': self.NODE_PADDING_X,
                'NODE_PADDING_Y': self.NODE_PADDING_Y,
                'NODE_CORNER_RADIUS': self.NODE_CORNER_RADIUS,
                
                # 边参数
                'EDGE_BASE_RADIUS': self.EDGE_BASE_RADIUS,
                'EDGE_RING_SPACING': self.EDGE_RING_SPACING,
                'EDGE_CONTROL_POINT_RATIO': self.EDGE_CONTROL_POINT_RATIO,
                'EDGE_BEND_RATIO': self.EDGE_BEND_RATIO,
                
                # 排列算法参数
                'RADIAL_BASE_R': self.RADIAL_BASE_R,
                'RADIAL_MAX_CONE': self.RADIAL_MAX_CONE,
                'RADIAL_PAD_ARC': self.RADIAL_PAD_ARC,
                'RADIAL_STRETCH_STEP': self.RADIAL_STRETCH_STEP,
                
                # 视图参数
                'SNAP_STEP': self.SNAP_STEP,
                'ALIGN_THRESHOLD': self.ALIGN_THRESHOLD,
                
                # 性能参数
                'HISTORY_LIMIT': self.HISTORY_LIMIT,
                'AUTOSAVE_DELAY': self.AUTOSAVE_DELAY,
            }
            
            with open(SETTINGS_PATH, 'w', encoding='utf-8') as f:
                json.dump(settings, f, ensure_ascii=False, indent=2)
            logger.info("所有设置已保存")
        except Exception as e:
            logger.error(f"保存设置失败: {e}")
            
    def open_settings(self):
        """打开设置对话框"""
        try:
            dialog = SettingsDialog(self)
            try:
                dialog.defaults_applied.connect(self._on_defaults_applied)
            except Exception:
                pass
            if dialog.exec_() == QDialog.Accepted:
                values = dialog.get_values()
                
                # 更新所有参数
                for key, value in values.items():
                    setattr(self, key, value)
                    
                # 保存设置
                self.save_all_settings()
                
                # 更新相关组件
                self._update_components_after_settings_change()
                
                QMessageBox.information(self, "成功", "设置已保存并应用。")
        except Exception as e:
            logger.error(f"打开设置对话框失败: {e}")
            QMessageBox.critical(self, "错误", f"打开设置失败: {e}")
            

    # ---------- 运行期默认值（仅用于后续新增子节点） ----------
    def get_runtime_defaults(self) -> dict:
        try:
            return dict(self._runtime_defaults)
        except Exception:
            # 回退到当前全局参数
            return {
                'NODE_FONT_SIZE': getattr(self, 'NODE_FONT_SIZE', 12),
                'NODE_PADDING_X': getattr(self, 'NODE_PADDING_X', 8),
                'NODE_PADDING_Y': getattr(self, 'NODE_PADDING_Y', 6),
                'NODE_CORNER_RADIUS': getattr(self, 'NODE_CORNER_RADIUS', 12),
            }

    def set_runtime_defaults(self, values: dict):
        if not hasattr(self, '_runtime_defaults'):
            self._runtime_defaults = {}
        self._runtime_defaults.update({
            k: v for k, v in values.items()
            if k in ('NODE_FONT_SIZE','NODE_PADDING_X','NODE_PADDING_Y','NODE_CORNER_RADIUS')
        })
        logger.info(f"runtime defaults updated: {self._runtime_defaults}")

    def _on_defaults_applied(self, values: dict):
        """设置对话框点了'应用'：只更新运行期默认值，不保存，不重绘"""
        self.set_runtime_defaults(values)

    def _update_components_after_settings_change(self):
        """设置更改后更新相关组件"""
        # 更新空间哈希
        if hasattr(self, '_spatial'):
            self._spatial.cell = max(40, self.SPATIAL_HASH_CELL_SIZE)
            
        # 更新自动保存定时器
        if hasattr(self, '_autosave_timer'):
            self._autosave_timer.setInterval(self.AUTOSAVE_DELAY)
            
        # 更新所有边的路径
        for edge in self.edges:
            edge.update_path()
            
        # 更新场景中的节点外观（如果需要）
        self.scene.update()

    # 添加大纲视图方法：
    def open_outline_view(self):
        """打开大纲视图"""
        if self.outline_window is None:
            self.outline_window = OutlineViewWindow(self)
        
        # 在显示前同步数据
        self.outline_window.sync_from_mindmap()
        self.outline_window.show()
        self.outline_window.raise_()  # 置于前台

    def show_detailed_error(self, title, message):
        """显示详细错误信息（开发阶段使用）"""
        detailed_msg = QMessageBox(self)
        detailed_msg.setIcon(QMessageBox.Critical)
        detailed_msg.setWindowTitle(title)
        detailed_msg.setText(message)
        exc = traceback.format_exc().strip()
        tb_text = exc if exc and exc != 'NoneType: None' else ''.join(traceback.format_stack(limit=25))
        detailed_msg.setDetailedText(tb_text)
        detailed_msg.exec_()

    def _apply_stylesheet(self):
        self.setStyleSheet("""
        QWidget { font-family: 'Segoe UI', 'Microsoft Yahei', 'PingFang SC', Arial; color:#203040; }
        QMainWindow { background: #EEF3F9; }
        #SidePanelLeft, #SidePanelRight { background: #F7FAFF; border: 1px solid #E3ECF7; border-radius: 14px; margin: 10px; }
        QLabel { font-weight:600; color:#2A3D66; }
        QPushButton { border: 1px solid #D6E2F1; padding: 10px 14px; margin: 8px 10px; min-height: 36px; border-radius: 10px; background: qlineargradient(x1:0,y1:0,x2:1,y2:1, stop:0 #ffffff, stop:1 #F3F8FF); }
        QPushButton:hover { background: #EBF3FF; }
        QPushButton:pressed { background: #E1ECFF; }
        QLineEdit { margin: 8px 10px; padding: 8px 10px; border-radius: 8px; border: 1px solid #D6E2F1; background:#FFFFFF; }
        QListWidget { margin: 8px 10px; border: 1px solid #D6E2F1; border-radius: 10px; background:#FFFFFF; }
        QScrollBar:vertical { width: 10px; background: transparent; }
        QScrollBar::handle:vertical { min-height:20px; background:#CFE0F4; border-radius:5px; }
        QScrollBar::add-line:vertical, QScrollBar::sub-line:vertical { height:0; }
        QScrollBar:horizontal { height: 10px; background: transparent; }
        QScrollBar::handle:horizontal { min-width:20px; background:#CFE0F4; border-radius:5px; }
        QScrollBar::add-line:horizontal, QScrollBar::sub-line:horizontal { width:0; }
        """)

    @error_handler("创建左侧面板时出错")
    def create_left_sidebar(self):
        panel = QWidget(objectName="SidePanelLeft")
        panel.setMaximumWidth(320)
        layout = QVBoxLayout(panel)

        btn_add = QPushButton("➕ 从选中节点添加 (N)")
        btn_add.clicked.connect(self.add_node_smart_from_selection)
        layout.addWidget(btn_add)

        btn_connect = QPushButton("🔗 手动连接（选中→选择目标）")
        btn_connect.clicked.connect(self.connect_nodes)
        layout.addWidget(btn_connect)

        btn_disconnect = QPushButton("✂️ 断开连接（对当前）")
        btn_disconnect.clicked.connect(self.disconnect_nodes)
        layout.addWidget(btn_disconnect)

        btn_import = QPushButton("📥 导入…")
        btn_import.clicked.connect(self.import_map)
        layout.addWidget(btn_import)

        btn_export = QPushButton("📤 导出…")
        btn_export.clicked.connect(self.export_map)
        layout.addWidget(btn_export)

        btn_radial = QPushButton("🟢 放射形排列")
        btn_radial.clicked.connect(self.arrange_radial)
        layout.addWidget(btn_radial)

        btn_tree = QPushButton("🌳 树形排列")
        btn_tree.clicked.connect(self.arrange_tree)
        layout.addWidget(btn_tree)

        btn_undo = QPushButton("↶ 撤销 (Ctrl+Z)")
        btn_undo.clicked.connect(self.undo)
        layout.addWidget(btn_undo)

        btn_redo = QPushButton("↷ 重做 (Ctrl+Y)")
        btn_redo.clicked.connect(self.redo)
        layout.addWidget(btn_redo)

        # 添加设置按钮
        btn_settings = QPushButton("⚙️ 排列参数设置")
        btn_settings.clicked.connect(self.open_settings)
        layout.addWidget(btn_settings)

        btn_outline = QPushButton("📄 大纲视图")
        btn_outline.clicked.connect(self.open_outline_view)
        layout.addWidget(btn_outline)

        layout.addStretch(1)
        return panel

    @error_handler("创建右侧面板时出错")
    def create_right_panel(self):
        panel = QWidget(objectName="SidePanelRight")
        panel.setMinimumWidth(360)
        panel.setMaximumWidth(480)
        layout = QVBoxLayout(panel)

        title = QLabel("📚 节点列表（按名称排序）")
        layout.addWidget(title)

        self.search_edit = QLineEdit()
        self.search_edit.setPlaceholderText("搜索节点名（支持模糊）")
        self.search_edit.textChanged.connect(self._on_search_text_changed)
        layout.addWidget(self.search_edit)

        self.list_widget = QListWidget()
        # 修改为单选模式
        self.list_widget.setSelectionMode(QListWidget.SingleSelection)
        self.list_widget.itemSelectionChanged.connect(self.on_list_selection_changed)
        layout.addWidget(self.list_widget, stretch=1)

        return panel

    def _on_search_text_changed(self):
        """搜索文本变化时的防抖处理"""
        self._search_timer.start(300)  # 300ms防抖

    @performance_monitor
    def refresh_node_list(self):
        """优化性能的节点列表刷新"""
        try:
            filter_text = (self.search_edit.text() if hasattr(self, 'search_edit') else "").strip().lower()
            
            # 使用生成器表达式提高性能
            names = sorted(self.nodes.keys(), key=lambda s: s.lower())
            
            # 避免不必要的UI更新
            self.list_widget.blockSignals(True)
            try:
                self.list_widget.clear()
                for name in names:
                    if filter_text and filter_text not in name.lower():
                        continue
                    item = QListWidgetItem(name)
                    self.list_widget.addItem(item)
                    if self.selected_node and name == self.selected_node.name:
                        item.setSelected(True)
            finally:
                self.list_widget.blockSignals(False)
                
        except Exception as e:
            logger.error(f"刷新节点列表失败: {e}")
            raise

    def on_scene_selection_changed(self):
        try:
            items = self.scene.selectedItems()
            nodes = [i for i in items if isinstance(i, MindMapNode)]
            
            if nodes:
                self.selected_node = nodes[0]  # 单选模式下只取第一个
                self.last_anchor_name = self.selected_node.name
            else:
                self.selected_node = None
                
            selected_name = self.selected_node.name if self.selected_node else None
            
            # 优化列表选择更新
            self.list_widget.blockSignals(True)
            try:
                # 清除所有选择
                for i in range(self.list_widget.count()):
                    item = self.list_widget.item(i)
                    item.setSelected(False)
                
                # 选择当前选中的节点
                if selected_name:
                    for i in range(self.list_widget.count()):
                        item = self.list_widget.item(i)
                        if item.text() == selected_name:
                            item.setSelected(True)
                            break
            finally:
                self.list_widget.blockSignals(False)
                
        except Exception as e:
            logger.error(f"场景选择变更处理失败: {e}")

    def on_list_selection_changed(self):
        try:
            selected_items = self.list_widget.selectedItems()
            if not selected_items:
                # 列表中没有选择，清除场景选择
                self.scene.blockSignals(True)
                try:
                    for item in list(self.scene.selectedItems()):
                        item.setSelected(False)
                    self.selected_node = None
                finally:
                    self.scene.blockSignals(False)
                return
                
            # 单选模式下只取第一个选中的项目
            wanted_name = selected_items[0].text()
            
            # 优化场景选择更新
            self.scene.blockSignals(True)
            try:
                # 清除所有选择
                for item in list(self.scene.selectedItems()):
                    item.setSelected(False)
                    
                # 选择对应的节点
                if wanted_name in self.nodes:
                    node = self.nodes[wanted_name]
                    node.setSelected(True)
                    self.selected_node = node
                    self.last_anchor_name = wanted_name
                    self.set_root_node(wanted_name)
            finally:
                self.scene.blockSignals(False)
                self.scene.selection_changed.emit()  # 手动触发一次
                
        except Exception as e:
            logger.error(f"列表选择变更处理失败: {e}")

    def select_node(self, node: MindMapNode):
        if node is None:
            return
            
        try:
            # 优化选择操作
            self.scene.blockSignals(True)
            try:
                # 清除所有选择
                for item in list(self.scene.selectedItems()):
                    item.setSelected(False)
                # 选择指定节点
                node.setSelected(True)
            finally:
                self.scene.blockSignals(False)
                
            self.selected_node = node
            self.last_anchor_name = node.name
            self.set_root_node(node.name)
            self.refresh_node_list()
            
        except Exception as e:
            logger.error(f"选择节点失败: {e}")

    def set_root_node(self, node_name: str):
        if node_name in self.nodes:
            self.root_node_name = node_name
            self.statusBar().showMessage(f"已将 '{node_name}' 设为根节点", 2000)
            logger.debug(f"设置根节点: {node_name}")

    @error_handler("确保根节点存在时出错")
    def _ensure_root_node_exists(self) -> str:
        """保证存在根节点，并返回有效根节点名称"""
        try:
            if not self.nodes:
                center = self.view.mapToScene(self.view.viewport().rect().center())
                node = self._create_node_at("思维导图", self._snap(center))
                self.set_root_node(node.name)
                self.select_node(node)
                logger.info("创建初始根节点")
                return node.name
                
            if self.root_node_name is None or self.root_node_name not in self.nodes:
                first_node_name = next(iter(self.nodes.keys()))
                self.set_root_node(first_node_name)
                logger.info(f"自动选择根节点: {first_node_name}")
                return first_node_name
                
            return self.root_node_name
            
        except Exception as e:
            logger.error(f"确保根节点存在失败: {e}")
            if self.nodes:
                first_node = next(iter(self.nodes.keys()))
                self.set_root_node(first_node)
                return first_node
            return None

    def _get_effective_root_node(self) -> str:
        """返回一个可用的根节点名称"""
        try:
            if self.root_node_name and self.root_node_name in self.nodes:
                return self.root_node_name
            if self.nodes:
                center = self.view.mapToScene(self.view.viewport().rect().center())
                closest_node = None
                min_distance = float('inf')
                
                # 优化距离计算
                for name, node in self.nodes.items():
                    node_pos = node.pos()
                    distance = math.hypot(node_pos.x() - center.x(), node_pos.y() - center.y())
                    if distance < min_distance:
                        min_distance = distance
                        closest_node = name
                        
                if closest_node:
                    self.set_root_node(closest_node)
                    return closest_node
                    
                first_node = list(self.nodes.keys())[0]
                self.set_root_node(first_node)
                return first_node
                
            return self._ensure_root_node_exists()
        except Exception as e:
            logger.error(f"获取有效根节点失败: {e}")
            return self._ensure_root_node_exists()

    def _ensure_unique_name(self, proposal: str, exclude=None, used_set=None) -> str:
        """确保名称唯一性，自动处理冲突"""
        # 处理空名称
        if not proposal or not proposal.strip():
            base = "节点"
        else:
            base = proposal.strip()
            
        taken = set(self.nodes.keys()) if used_set is None else set(used_set)
        
        if base and ((base not in taken) or base == exclude):
            return base
            
        i = 1
        while True:
            cand = f"{base} {i}"
            if (cand not in taken) or cand == exclude:
                logger.debug(f"名称冲突解决: '{proposal}' -> '{cand}'")
                return cand
            i += 1

    def _next_color(self) -> QColor:
        c = self._palette_cycle[self._next_color_idx % len(self._palette_cycle)]
        self._next_color_idx += 1
        return QColor(c)

    @error_handler("更新节点名称时出错")
    def _update_node_name_in_graph(self, node: MindMapNode, old_name: str, new_name: str):
        """原子性地更新图中的节点名称"""
        if old_name == new_name:
            return
            
        if new_name in self.nodes and new_name != old_name:
            QMessageBox.warning(self, "名称冲突", f"名称 '{new_name}' 已被使用")
            # 不再直接调用 node.set_name(old_name)，避免递归
            return
            
        try:
            if self.graph.has_node(old_name):
                pos = self.graph.nodes[old_name].get('pos', (0, 0))
                color = self.graph.nodes[old_name].get('color', "#7EC8E3")
                
                self.graph = nx.relabel_nodes(self.graph, {old_name: new_name})
                self.graph.nodes[new_name]['pos'] = pos
                self.graph.nodes[new_name]['color'] = color
                
                self.nodes[new_name] = self.nodes.pop(old_name)
                
                if self.root_node_name == old_name:
                    self.root_node_name = new_name
                if self.selected_node and self.selected_node.name == old_name:
                    self.selected_node = node
                if self.last_anchor_name == old_name:
                    self.last_anchor_name = new_name
                    
            self.refresh_node_list()
            self.push_history("rename")
            logger.info(f"节点重命名: '{old_name}' -> '{new_name}'")
            
        except Exception as e:
            logger.error(f"节点重命名失败: {e}")
            QMessageBox.critical(self, "错误", f"重命名失败: {e}")
            # 不再回滚节点名称，避免递归

    def _is_pos_free(self, pos: QPointF, min_dist=140) -> bool:
        # spatial-hash accelerated neighborhood test
        px, py = pos.x(), pos.y()
        r_new = max(min_dist * 0.5, self._node_radius_px(None))
        if hasattr(self, '_spatial'):
            for nm in self._spatial.neighbors(px, py, r_new):
                other = self.nodes.get(nm)
                if not other:
                    continue
                r_sum = self._spatial.radius.get(nm, self._node_radius_px(nm)) + r_new
                dx = other.x() - px
                dy = other.y() - py
                if (dx*dx + dy*dy) ** 0.5 < r_sum:
                    return False
            return True
        # fallback: scan all
        for other in self.nodes.values():
            dx = other.x() - px
            dy = other.y() - py
            if math.hypot(dx, dy) < min_dist:
                return False
        return True

    def _node_radius_px(self, name=None):
        # estimate node "radius" using bounding rect diagonal / 2 plus small buffer
        try:
            if name and name in self.nodes:
                rect = self.nodes[name].boundingRect()
                diag = (rect.width()**2 + rect.height()**2) ** 0.5
            else:
                diag = max(120.0, float(self._calculate_average_node_size()))
        except Exception:
            diag = 140.0
        return diag * 0.5 + 10.0

    def _snap(self, p: QPointF) -> QPointF:
        step = self.snap_step
        return QPointF(round(p.x() / step) * step, round(p.y() / step) * step)

    def _pick_angle_in_largest_gap(self, anchor_item: 'MindMapNode') -> float:
        anchor_pos = anchor_item.pos()
        neighbor_names = list(self.graph.neighbors(anchor_item.name)) if self.graph.has_node(anchor_item.name) else []
        angles = []
        for nb in neighbor_names:
            if nb in self.nodes:
                p = self.nodes[nb].pos()
                angles.append(_angle_between(anchor_pos, p))
        if not angles:
            return 0.0
        angles = sorted(angles)
        twopi = 2.0 * math.pi
        gaps = []
        for i in range(len(angles)):
            a = angles[i]
            b = angles[(i + 1) % len(angles)]
            gap = (b - a) if i < len(angles) - 1 else (b + twopi - a)
            gaps.append((gap, a, b))
        gaps.sort(key=lambda x: x[0], reverse=True)
        max_gap, a, b = gaps[0]
        mid = a + max_gap / 2.0
        return _angle_normalize(mid)

    @performance_monitor
    @error_handler("智能添加节点时出错")
    def add_node_smart_from_selection(self, text: str = None, color: QColor = None):
        """优化性能的智能节点添加"""
        self._ensure_root_node_exists()
        anchor_item = self.selected_node if self.selected_node else self.nodes[self._get_effective_root_node()]

        name = self._ensure_unique_name((text or "子节点").strip())
        color = color if isinstance(color, QColor) else self._next_color()

        ang_center, radius = self._find_free_slot(anchor_item)

        base = anchor_item.pos()
        px = base.x() + radius * math.cos(ang_center)
        py = base.y() + radius * math.sin(ang_center)
        pos = self._snap(QPointF(px, py))

        node_item = self._create_node_at(name, pos, color)
        self.graph.add_edge(anchor_item.name, name)
        self.create_edge(anchor_item, node_item)

        self.select_node(node_item)
        self.push_history("add_child")
        logger.info(f"添加子节点: {name} -> {anchor_item.name}")

    def _neighbors_angles(self, anchor_item: 'MindMapNode'):
        """优化邻居角度计算"""
        center = anchor_item.pos()
        angles = []
        if self.graph.has_node(anchor_item.name):
            for nb in self.graph.neighbors(anchor_item.name):
                if nb in self.nodes:
                    p = self.nodes[nb].pos()
                    angles.append(_angle_between(center, p))
        return sorted(angles)

    def _min_radius_to_fit_gap(self, gap_width: float, min_chord: float) -> float:
        gap = max(1e-3, gap_width)
        s = math.sin(gap / 2.0)
        if s <= 1e-6:
            return float("inf")
        return (min_chord / 2.0) / s

    def _spiral_offsets(self, step_deg: float, limit_deg: float):
        step = math.radians(max(1.0, step_deg))
        limit = math.radians(max(step_deg, limit_deg))
        k = 1
        while k * step <= limit + 1e-9:
            yield +k * step
            yield -k * step
            k += 1

    def _calculate_average_node_size(self):
        """计算所有节点的平均大小"""
        if not self.nodes:
            return 140  # 默认值
            
        total_width = 0
        total_height = 0
        count = 0
        
        for node in self.nodes.values():
            rect = node.boundingRect()
            total_width += rect.width()
            total_height += rect.height()
            count += 1
        
        if count == 0:
            return 140
            
        avg_width = total_width / count
        avg_height = total_height / count
        # 使用节点对角线长度作为基础弦长
        avg_diagonal = math.sqrt(avg_width**2 + avg_height**2)
        return avg_diagonal

    @performance_monitor
    def _find_free_slot(self, anchor_item, base_radius=160.0, ring=160.0, min_chord=None, 
                       pad_deg=8.0, global_min_dist=140.0, max_rings=6):
        """旗舰版：父向锥形 + 黄金角细分 + 泊松盘约束的空位搜索"""
        # 1) 参数与动态量
        if base_radius <= 0.0:
            base_radius = max(120.0, float(self.TARGET_EDGE) * 0.9)
        if ring <= 0.0:
            ring = float(self.TARGET_EDGE)
        if min_chord is None:
            avg_diag = self._calculate_average_node_size()
            min_chord = max(80.0, avg_diag * 1.2 * self.MIN_CHORD_RATIO)

        center = anchor_item.pos()
        twopi = 2.0 * math.pi
        pad = math.radians(max(2.0, pad_deg))
        angles = self._neighbors_angles(anchor_item)

        # 2) "父向锥形"与"兄弟连续角"偏好
        try:
            anchor_level = self._get_node_level(anchor_item.name)
        except Exception:
            anchor_level = 0
        parent_name = None
        if self.graph.has_node(anchor_item.name):
            al = anchor_level
            for nb in self.graph.neighbors(anchor_item.name):
                try:
                    if self._get_node_level(nb) < al:
                        parent_name = nb
                        break
                except Exception:
                    pass
        if parent_name and parent_name in self.nodes:
            pref_angle = _angle_between(self.nodes[parent_name].pos(), anchor_item.pos())
        else:
            pref_angle = 0.0  # 根或无父：默认向右

        # 兄弟"连续角"记忆：让新增子节点沿着上一个子角继续"扇出"
        meta = self.graph.nodes.get(anchor_item.name, {})
        last_child_angle = meta.get('last_child_angle', None)
        golden = math.radians(137.50776405003785)  # 黄金角
        if last_child_angle is not None:
            pref_angle = last_child_angle + golden

        # 3) 可用扇区
        if not angles:
            a0 = _angle_normalize(pref_angle - math.pi/2 + pad)
            a1 = _angle_normalize(pref_angle + math.pi/2 - pad)
            gap_width = (a1 - a0) % twopi
            ang_center = _angle_normalize(pref_angle)
            sector = (a0, gap_width)
        else:
            gaps = []
            for i, a in enumerate(angles):
                b = angles[(i + 1) % len(angles)]
                gap = (b - a) if i < len(angles) - 1 else (b + twopi - a)
                gaps.append((gap, a))
            gaps.sort(key=lambda x: x[0], reverse=True)
            gap_width, a = gaps[0]
            ang_center = _angle_normalize(a + gap_width / 2.0)
            a0 = (a + pad) % twopi
            gap_width = max(1e-3, gap_width - 2 * pad)
            sector = (a0, gap_width)

        # radius needed to fit chord in gap
        def _need_radius(width, chord):
            s = math.sin(max(1e-6, width) / 2.0)
            return (chord * 0.5) / s if s > 1e-6 else float('inf')

        need_r = _need_radius(sector[1], min_chord)
        r0 = max(base_radius, need_r)
        if r0 > base_radius:
            rings_up = math.ceil((r0 - base_radius) / ring)
            r0 = base_radius + rings_up * ring

        # 角度候选（扇区中心优先，然后对称扩展）
        def angle_candidates(center_angle, limit_deg):
            yield center_angle
            step = math.radians(10.0)
            limit = math.radians(max(10.0, limit_deg))
            k = 1
            while k * step <= limit + 1e-9:
                yield _angle_normalize(center_angle + k * step)
                yield _angle_normalize(center_angle - k * step)
                k += 1

        # 父向锥限制（孩子越多锥越窄）
        cone_deg = max(60.0, 120.0 - 10.0 * len(angles))
        def in_sector(x):
            a0, width = sector
            hi = (a0 + width) % twopi
            if width >= twopi - 1e-3:
                ok = True
            elif hi < a0:
                ok = (x >= a0 or x <= hi)
            else:
                ok = (a0 <= x <= hi)
            delta = abs((_angle_normalize(x - pref_angle) + math.pi) % (2*math.pi) - math.pi)
            return ok and (delta <= math.radians(cone_deg))

        angle_limit_deg = min(170.0, math.degrees(sector[1]) * 0.5)
        for ring_i in range(max_rings + 1):
            r = r0 + ring_i * ring
            for ang in angle_candidates(ang_center, angle_limit_deg):
                if not in_sector(ang):
                    continue
                # 轻微抖动
                jitter = 0.0 if ring_i == 0 else min(8.0, ring * 0.02)
                x = center.x() + r * math.cos(ang) + (jitter * (0.5 - (hash((anchor_item.name, ang, r)) & 1023) / 1023.0))
                y = center.y() + r * math.sin(ang) + (jitter * (0.5 - (hash((r, ang, anchor_item.name)) & 1023) / 1023.0))
                p = self._snap(QPointF(x, y))
                if self._is_pos_free(p, global_min_dist):
                    # 记录"上次子角"
                    self.graph.nodes[anchor_item.name]['last_child_angle'] = float(ang)
                    return ang, r

        # 兜底
        self.graph.nodes[anchor_item.name]['last_child_angle'] = float(ang_center)
        return ang_center, r0 + ring

    def _create_node_at(self, name: str, pos: QPointF, color: QColor=None) -> 'MindMapNode':
        if color is None:
            color = self._next_color()
            
        self.graph.add_node(name)
        self.graph.nodes[name]['pos'] = (pos.x(), pos.y())
        self.graph.nodes[name]['color'] = qcolor_to_hex(color)
        
        # 从运行期默认值获取新节点的样式
        try:
            rdefs = self.get_runtime_defaults()
        except Exception:
            rdefs = {}
        node_item = MindMapNode(
            name,
            color,
            font_size=int(rdefs.get('NODE_FONT_SIZE', getattr(self, 'NODE_FONT_SIZE', 12))),
            pad_x=int(rdefs.get('NODE_PADDING_X', getattr(self, 'NODE_PADDING_X', 8))),
            pad_y=int(rdefs.get('NODE_PADDING_Y', getattr(self, 'NODE_PADDING_Y', 6))),
            corner_radius=int(rdefs.get('NODE_CORNER_RADIUS', getattr(self, 'NODE_CORNER_RADIUS', 12)))
        )
        node_item.setPos(pos)
        node_item.moved.connect(self._on_node_moved)
        node_item.color_changed.connect(lambda _: self._on_node_color_changed(name))
        node_item.renamed.connect(self._on_node_renamed)
        
        self.scene.addItem(node_item)
        self.nodes[name] = node_item
        # 空间哈希登记
        try:
            self._pos_cache[name] = (pos.x(), pos.y())
            if hasattr(self, '_spatial'):
                self._spatial.insert(name, pos.x(), pos.y(), self._node_radius_px(name))
        except Exception:
            pass

        
        if self.root_node_name is None:
            self.root_node_name = name
            
        logger.debug(f"创建节点: {name} at ({pos.x():.1f}, {pos.y():.1f})")
        return node_item

    def _on_node_moved(self, node):
        if not hasattr(self, 'nodes') or node.name not in self.nodes:
            return
            
        try:
            self.scene.update_connections_for(node)
            
            if hasattr(self, '_history_timer') and self._history_timer.isActive():
                self._history_timer.stop()
            self._history_timer.start(250)
            
            if hasattr(self, '_autosave_timer') and self._autosave_timer.isActive():
                self._autosave_timer.stop()
            self._autosave_timer.start(300)
            
            # 修复空间哈希位置同步
            try:
                oldx, oldy = self._pos_cache.get(node.name, (node.x(), node.y()))
                if hasattr(self, '_spatial') and self._spatial is not None:
                    self._spatial.move(node.name, oldx, oldy, node.x(), node.y())
                self._pos_cache[node.name] = (node.x(), node.y())
            except Exception as e:
                logger.warning(f"空间哈希更新失败: {e}")
                # 重试一次
                try:
                    if hasattr(self, '_spatial') and self._spatial is not None:
                        self._spatial.remove(node.name, oldx, oldy)
                        self._spatial.insert(node.name, node.x(), node.y(), self._node_radius_px(node.name))
                    self._pos_cache[node.name] = (node.x(), node.y())
                except Exception as retry_e:
                    logger.error(f"空间哈希重试更新失败: {retry_e}")
                    # 如果重试也失败，重建整个空间哈希
                    self._rebuild_spatial_hash()
        except Exception as e:
            logger.error(f"节点移动处理错误: {e}")

    def _rebuild_spatial_hash(self):
        """重建整个空间哈希"""
        try:
            if hasattr(self, '_spatial') and self._spatial is not None:
                self._spatial = _SpatialHash(cell=self.SPATIAL_HASH_CELL_SIZE)
                for name, node in self.nodes.items():
                    if name in self._pos_cache:
                        x, y = self._pos_cache[name]
                    else:
                        x, y = node.x(), node.y()
                        self._pos_cache[name] = (x, y)
                    self._spatial.insert(name, x, y, self._node_radius_px(name))
                logger.info("空间哈希已重建")
        except Exception as e:
            logger.error(f"重建空间哈希失败: {e}")

    def _on_node_color_changed(self, name: str):
        if name in self.nodes and self.graph.has_node(name):
            self.graph.nodes[name]['color'] = qcolor_to_hex(self.nodes[name].color)
        for edge in list(self.scene.edges_by_node[self.nodes[name]]):
            edge.set_color(QColor(120, 120, 120))
        self.push_history("color")

    def _on_node_renamed(self, node, old_name, new_name):
        self._update_node_name_in_graph(node, old_name, new_name)

    def _get_node_level(self, node_name):
        """计算节点在树结构中的层级（从根节点开始的深度）"""
        # 如果缓存不存在或为空，重新计算
        if not hasattr(self, '_node_level_cache') or not self._node_level_cache:
            self._rebuild_node_level_cache()
        
        # 如果节点不在缓存中，也重新计算
        if node_name not in self._node_level_cache:
            self._rebuild_node_level_cache()
            
        return self._node_level_cache.get(node_name, 0)

    def _rebuild_node_level_cache(self):
        """重建节点层级缓存"""
        self._node_level_cache = {}
        root = self._get_effective_root_node()
        if not root:
            return
            
        visited = set()
        queue = [(root, 0)]
        while queue:
            current, level = queue.pop(0)
            if current in visited:
                continue
            visited.add(current)
            self._node_level_cache[current] = level
            if self.graph.has_node(current):
                for nb in self.graph.neighbors(current):
                    if nb not in visited:
                        queue.append((nb, level + 1))
                      
    @error_handler("删除节点时出错")
    def delete_specific_node(self, node_item: MindMapNode):
        """安全的节点删除"""
        if node_item is None or not hasattr(node_item, 'name'):
            return
            
        try:
            name = node_item.name
            self._autosave_timer.start(300)
            # 空间哈希删除登记
            try:
                if hasattr(self, '_spatial'):
                    self._spatial.remove(name, node_item.x(), node_item.y())
                self._pos_cache.pop(name, None)
            except Exception:
                pass
            
            # 安全断开信号连接
            try:
                node_item.moved.disconnect()
            except (TypeError, RuntimeError):
                pass  # 没有连接或已经断开
                
            try:
                node_item.color_changed.disconnect()
            except (TypeError, RuntimeError):
                pass  # 没有连接或已经断开
                
            try:
                node_item.renamed.disconnect()
            except (TypeError, RuntimeError):
                pass  # 没有连接或已经断开
                
            # 处理根节点重新选择
            if name == self.root_node_name:
                remaining_nodes = [n for n in self.nodes.keys() if n != name]
                if remaining_nodes:
                    self.root_node_name = remaining_nodes[0]
                    self.statusBar().showMessage(f"已自动将 '{self.root_node_name}' 设为新根节点", 2000)
                    logger.info(f"自动设置新根节点: {self.root_node_name}")
                else:
                    self.root_node_name = None
                    
            # 从图中移除
            if self.graph.has_node(name):
                self.graph.remove_node(name)
                
            # 清理边连接
            edges_to_remove = []
            if node_item in self.scene.edges_by_node:
                for edge in list(self.scene.edges_by_node[node_item]):
                    self.scene.remove_connection(edge)
                    if edge in self.edges:
                        self.edges.remove(edge)
                    edges_to_remove.append(edge)
                    
            # 从场景中移除
            for edge in edges_to_remove:
                if edge.scene() == self.scene:
                    self.scene.removeItem(edge)
                    
            if node_item.scene() == self.scene:
                self.scene.removeItem(node_item)
                
            # 清理引用
            if name in self.nodes:
                del self.nodes[name]
                
            if self.selected_node is node_item:
                self.selected_node = None
            if self.last_anchor_name == name:
                self.last_anchor_name = None
                
            # 清空层级缓存
            if hasattr(self, '_node_level_cache'):
                self._node_level_cache.clear()
                
            self.refresh_node_list()
            self.push_history("delete")
            
        except Exception as e:
            logger.error(f"删除节点失败: {e}")
            QMessageBox.critical(self, "错误", f"删除节点时出错: {e}")

    def delete_node(self):
        if not self.selected_node:
            QMessageBox.information(self, "提示", "请先选择一个节点。")
            return
        self.delete_specific_node(self.selected_node)

    def create_edge(self, node1: MindMapNode, node2: MindMapNode):
        edge = MindMapEdge(node1, node2, QColor(120, 120, 120))
        self.scene.addItem(edge)
        self.scene.add_connection(edge, node1, node2)
        self.edges.append(edge)
        return edge

    @error_handler("连接节点时出错")
    def connect_nodes(self):
        self._ensure_root_node_exists()

        if not self.selected_node:
            QMessageBox.warning(self, "错误", "请先选择一个节点！")
            return
        src = self.selected_node.name
        available = [n for n in self.nodes if n != src and not self.graph.has_edge(src, n)]
        if not available:
            QMessageBox.information(self, "提示", "没有可连接的节点！")
            return
        target_name, ok = QInputDialog.getItem(self, "连接节点", "选择要连接的节点:", available, 0, False)
        if ok and target_name:
            self.graph.add_edge(src, target_name)
            self.create_edge(self.nodes[src], self.nodes[target_name])
            # 清空层级缓存
            if hasattr(self, '_node_level_cache'):
                self._node_level_cache.clear()
            self.push_history("connect")
            logger.info(f"连接节点: {src} -> {target_name}")

    @error_handler("断开节点连接时出错")
    def disconnect_nodes(self):
        self._ensure_root_node_exists()

        if not self.selected_node:
            QMessageBox.warning(self, "错误", "请先选择一个节点！")
            return
        src = self.selected_node.name
        neighbors = list(self.graph.neighbors(src))
        if not neighbors:
            QMessageBox.information(self, "提示", "该节点没有连接！")
            return
        target_name, ok = QInputDialog.getItem(self, "断开连接", "选择要断开的节点:", neighbors, 0, False)
        if ok and target_name:
            if self.graph.has_edge(src, target_name):
                self.graph.remove_edge(src, target_name)
            for edge in list(self.scene.edges_by_node[self.selected_node]):
                pair = {edge.node_pair[0].name, edge.node_pair[1].name}
                if pair == {src, target_name}:
                    self.scene.remove_connection(edge)
                    self.scene.removeItem(edge)
                    if edge in self.edges:
                        self.edges.remove(edge)
                    break
            # 清空层级缓存
            if hasattr(self, '_node_level_cache'):
                self._node_level_cache.clear()
            self.push_history("disconnect")
            logger.info(f"断开连接: {src} - {target_name}")

    def update_all_edges(self):
        for e in self.edges:
            e.update_path()

    def import_map(self):
        fmt, ok = QInputDialog.getItem(self, "选择导入格式", "请选择格式:", ["JSON", "Markdown"], 0, False)
        if not ok:
            return
        if fmt == "JSON":
            self.import_map_json()
        else:
            self.import_map_markdown()

    def export_map(self):
        fmt, ok = QInputDialog.getItem(self, "选择导出格式", "请选择格式:", ["JSON", "Markdown"], 0, False)
        if not ok:
            return
        if fmt == "JSON":
            self.export_map_json()
        else:
            self.export_map_markdown()

    def _sync_graph_from_scene(self):
        for name, item in self.nodes.items():
            if self.graph.has_node(name):
                self.graph.nodes[name]['pos'] = (item.x(), item.y())
                self.graph.nodes[name]['color'] = qcolor_to_hex(item.color)

    @error_handler("导入JSON时出错")
    def import_map_json(self):
        """导入JSON（增强版，兼容多种格式）"""
        file_name, _ = QFileDialog.getOpenFileName(
            self, "导入思维导图 JSON", "", "JSON 文件 (*.json);;所有文件 (*)"
        )
        if not file_name:
            return
        
        try:
            with open(file_name, "r", encoding='utf-8') as f:
                data = json.load(f)
            
            # 处理不同格式的JSON文件
            if isinstance(data, dict) and "type" in data and data["type"] == "mindmap":
                # 新格式：包含元数据的思维导图
                graph_data = data.get("data", {})
                g = nx.node_link_graph(graph_data, edges="links")
                root_node = data.get("root_node")
            else:
                # 旧格式或标准格式
                g = nx.node_link_graph(data, edges="links")
                root_node = None
            
            # 处理图数据
            for n in g.nodes:
                if 'pos' not in g.nodes[n]:
                    g.nodes[n]['pos'] = (0.0, 0.0)
                if 'color' not in g.nodes[n]:
                    g.nodes[n]['color'] = "#7EC8E3"
            
            self.graph = g
            self.refresh_scene()
            
            # 设置根节点
            if root_node and root_node in self.nodes:
                self.root_node_name = root_node
            elif self.nodes:
                self.root_node_name = list(self.nodes.keys())[0]
            
            self.push_history("import_json")
            QMessageBox.information(self, "成功", "JSON 导入成功！")
            
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导入失败：{e}")

    @error_handler("导出JSON时出错")
    def export_map_json(self):
        """导出为JSON（增强版，兼容大纲视图）"""
        if not self.graph.nodes:
            QMessageBox.warning(self, "错误", "没有内容可以导出！")
            return
        
        self._sync_graph_from_scene()
        
        # 构建兼容大纲视图的数据结构
        export_data = {
            "type": "mindmap",
            "version": "2.0",
            "data": nx.node_link_data(self.graph, edges="links"),
            "root_node": self.root_node_name,
            "metadata": {
                "export_time": QDateTime.currentDateTime().toString(Qt.ISODate),
                "node_count": len(self.graph.nodes),
                "edge_count": len(self.graph.edges)
            }
        }
        
        file_name, _ = QFileDialog.getSaveFileName(
            self, "导出思维导图 JSON", "mindmap.json", "JSON 文件 (*.json)"
        )
        if not file_name:
            return
        
        try:
            with open(file_name, "w", encoding='utf-8') as f:
                json.dump(export_data, f, ensure_ascii=False, indent=2)
            QMessageBox.information(self, "成功", "JSON 导出成功！")
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出失败：{e}")


    @error_handler("导入Markdown时出错")
    def import_map_markdown(self):
        file_name, _ = QFileDialog.getOpenFileName(self, "导入 Markdown 列表", "", "Markdown 文件 (*.md *.markdown);;所有文件 (*)")
        if not file_name:
            return
        try:
            text = Path(file_name).read_text(encoding='utf-8')
            used = set(); nodes = []; edges = []
            stack = []
            lines = text.splitlines()
            def ensure_unique(nm):
                base = nm.strip() or "节点"
                if base not in used:
                    used.add(base); return base
                i = 1
                while True:
                    cand = f"{base} {i}"
                    if cand not in used:
                        used.add(cand); return cand
                    i += 1
            for raw in lines:
                m = re.match(r"^(\s*)([-*+])\s+(.*\S)\s*$", raw)
                if not m: continue
                indent = len(m.group(1).replace('\t','    '))
                name = ensure_unique(m.group(3))
                nodes.append(name)
                while stack and indent <= stack[-1][0]:
                    stack.pop()
                if stack:
                    parent = stack[-1][1]
                    edges.append((parent, name))
                stack.append((indent, name))
            
            # 保存旧状态用于恢复
            old_graph = self.graph.copy() if hasattr(self, 'graph') else None
            old_nodes = self.nodes.copy() if hasattr(self, 'nodes') else {}
            old_root = self.root_node_name
            old_selected = self.selected_node.name if self.selected_node else None
            
            try:
                self.graph.clear()
                self.nodes.clear(); self.edges.clear(); self.scene.clear(); self.scene.edges_by_node.clear()
                
                for name in nodes:
                    self._create_node_at(name, QPointF(0,0), self._next_color())
                for u, v in edges:
                    if self.graph.has_node(u) and self.graph.has_node(v):
                        self.graph.add_edge(u, v)
                        self.create_edge(self.nodes[u], self.nodes[v])
                root = nodes[0] if nodes else None
                self.arrange_tree(root=root)
                if self.nodes:
                    self.root_node_name = list(self.nodes.keys())[-1]
                    
                # 清空层级缓存
                if hasattr(self, '_node_level_cache'):
                    self._node_level_cache.clear()
                    
                self.push_history("import_md")
                QMessageBox.information(self, "成功", "Markdown 导入成功！")
                logger.info(f"成功导入Markdown文件: {file_name}")
            except Exception as inner_e:
                # 恢复所有状态
                if old_graph is not None:
                    self.graph = old_graph
                if old_nodes:
                    self.nodes = old_nodes
                self.root_node_name = old_root
                if old_selected and old_selected in self.nodes:
                    self.select_node(self.nodes[old_selected])
                self.refresh_scene()
                raise inner_e
                
        except Exception as e:
            logger.error(f"导入Markdown失败: {e}")
            QMessageBox.critical(self, "错误", f"导入失败：{e}")

    @error_handler("导出Markdown时出错")
    def export_map_markdown(self):
        if not self.graph.nodes:
            QMessageBox.warning(self, "错误", "没有内容可以导出！")
            return
        def bfs_tree_lines(root):
            T = nx.bfs_tree(self.graph, root)
            children = defaultdict(list)
            for u, v in T.edges():
                children[u].append(v)
            for k in list(children.keys()):
                children[k].sort(key=lambda s: s.lower())
            lines = []
            def rec(n, d):
                lines.append("  "*d + "- " + n)
                for c in children.get(n, []):
                    rec(c, d+1)
            rec(root, 0)
            return lines
        roots = []
        if self.selected_node:
            roots = [self.selected_node.name]
        else:
            for comp in nx.connected_components(self.graph):
                comp = list(comp)
                root = min(comp, key=lambda x: self.graph.degree[x])
                roots.append(root)
        all_lines = []
        for r in roots:
            all_lines.extend(bfs_tree_lines(r))
            all_lines.append("")
        md_text = "\n".join(all_lines).rstrip()+"\n"
        file_name, _ = QFileDialog.getSaveFileName(self, "导出为 Markdown", "mindmap.md", "Markdown 文件 (*.md *.markdown)")
        if not file_name:
            return
        try:
            Path(file_name).write_text(md_text, encoding='utf-8')
            QMessageBox.information(self, "成功", "Markdown 导出成功！")
            logger.info(f"成功导出Markdown文件: {file_name}")
        except Exception as e:
            logger.error(f"导出Markdown失败: {e}")
            QMessageBox.critical(self, "错误", f"导出失败：{e}")

    @performance_monitor
    @error_handler("径向排列时出错")
    def arrange_radial(self, root=None):
        # 使用用户设置的参数
        BASE_R = self.RADIAL_BASE_R
        RING   = self.TARGET_EDGE
        
        # 动态计算最小弦长：基于节点实际大小
        avg_diagonal = self._calculate_average_node_size()
        MIN_CHORD = avg_diagonal * 1.5 * self.MIN_CHORD_RATIO
        
        MAX_CONE_NONROOT = math.radians(self.RADIAL_MAX_CONE)
        PAD_ARC = math.radians(self.RADIAL_PAD_ARC)
        STRETCH_STEP = self.RADIAL_STRETCH_STEP
        MAX_EXTRA_STRETCH = self.MAX_EXTRA_STRETCH * self.TARGET_EDGE
        MAX_RINGS_PER_LEVEL = 4

        effective_root = self._get_effective_root_node()
        if not effective_root:
            return
        if root is None or root not in self.graph:
            root = effective_root
        self.set_root_node(root)

        try:
            T = nx.bfs_tree(self.graph, root)
        except nx.NetworkXError:
            T = nx.bfs_tree(self.graph, effective_root)

        children = defaultdict(list)
        for u, v in T.edges():
            children[u].append(v)
        for k in children:
            children[k].sort(key=lambda s: s.lower())

        center = self.view.mapToScene(self.view.viewport().rect().center())
        self._set_node_pos(root, self._snap(center))

        angle_of = {root: 0.0}
        radius_of = {root: 0.0}
        twopi = 2.0 * math.pi

        def clamp_sector_to_cone(a0, a1, center_ang, cone_width):
            half = cone_width / 2.0
            lo = center_ang - half
            hi = center_ang + half
            s = max(a0, lo)
            e = min(a1, hi)
            if e <= s:
                mid = (a0 + a1) / 2.0
                s = mid - min(cone_width, (a1 - a0)) * 0.25
                e = mid + min(cone_width, (a1 - a0)) * 0.25
            return s, e

        def delta_required(rad):
            x = min(0.999999, max(0.0, MIN_CHORD / max(1e-6, 2.0 * rad)))
            return 2.0 * math.asin(x)

        def assign(n: str, depth: int, a0: float, a1: float, r_parent: float):
            ch = children.get(n, [])
            if not ch:
                return

            parent_dir = angle_of.get(n, (a0 + a1) / 2.0)
            if depth == 0:
                use_a0, use_a1 = a0 + PAD_ARC, a1 - PAD_ARC
            else:
                raw_a0, raw_a1 = a0 + PAD_ARC, a1 - PAD_ARC
                use_a0, use_a1 = clamp_sector_to_cone(raw_a0, raw_a1, parent_dir, min(MAX_CONE_NONROOT, raw_a1 - raw_a0))
            usable_width = max(0.0, use_a1 - use_a0)

            r_base = max(r_parent + RING, BASE_R + RING * (depth + 1))

            m = len(ch)
            if m == 1:
                angles = [(use_a0 + use_a1) / 2.0]
                ring_of_idx = [0]
                ring_radii = [r_base]
            else:
                need = delta_required(r_base)
                cap_base = int(usable_width / need) + 1

                ring_radii = [r_base]
                counts = []

                if cap_base >= m:
                    counts = [m]
                else:
                    extra = 0.0
                    stretched_cap = cap_base
                    while stretched_cap < m and extra < MAX_EXTRA_STRETCH:
                        extra += STRETCH_STEP
                        need2 = delta_required(r_base + extra)
                        stretched_cap = int(usable_width / need2) + 1
                    if stretched_cap >= m:
                        ring_radii[0] = r_base + extra
                        counts = [m]
                    else:
                        counts = []
                        total = 0
                        ring_radii = [r_base]
                        while total < m and len(ring_radii) < MAX_RINGS_PER_LEVEL:
                            cur_r = ring_radii[-1]
                            cap = int(usable_width / delta_required(cur_r)) + 1
                            if cap < 2 and (m - total) > 1:
                                cap = 2
                            put = min(cap, m - total)
                            counts.append(put)
                            total += put
                            if total < m:
                                ring_radii.append(cur_r + RING)

                        if total < m:
                            need_more = m - total
                            last_r = ring_radii[-1]
                            cap_last = int(usable_width / delta_required(last_r)) + 1
                            extra2 = 0.0
                            while cap_last < need_more and extra2 < MAX_EXTRA_STRETCH:
                                extra2 += STRETCH_STEP
                                cap_last = int(usable_width / delta_required(last_r + extra2)) + 1
                            ring_radii[-1] = last_r + extra2
                            counts.append(need_more)
                            total += need_more

                if m > 1:
                    step = usable_width / (m - 1)
                    angles = [use_a0 + i * step for i in range(m)]
                else:
                    angles = [(use_a0 + use_a1) / 2.0]

                ring_of_idx = []
                idx = 0
                for ring_i, cnt in enumerate(counts):
                    for _ in range(cnt):
                        ring_of_idx.append(ring_i)
                        idx += 1

            for idx, c in enumerate(ch):
                ang = angles[idx]
                r_child = ring_radii[ring_of_idx[idx]]
                x = center.x() + r_child * math.cos(ang)
                y = center.y() + r_child * math.sin(ang)
                p = self._snap(QPointF(x, y))
                self._set_node_pos(c, p)
                angle_of[c] = ang
                radius_of[c] = r_child

            m = len(ch)
            boundaries = []
            if m == 1:
                boundaries = [(use_a0, use_a1)]
            else:
                mids = [ (angles[i] + angles[i+1]) / 2.0 for i in range(m - 1) ]
                boundaries.append((use_a0, mids[0] - PAD_ARC * 0.5))
                for i in range(m - 2):
                    boundaries.append((mids[i] + PAD_ARC * 0.5, mids[i+1] - PAD_ARC * 0.5))
                boundaries.append((mids[-1] + PAD_ARC * 0.5, use_a1))

            for (c, (sa0, sa1), idx) in zip(ch, boundaries, range(len(ch))):
                assign(c, depth + 1, sa0, sa1, ring_radii[ring_of_idx[idx]])

        assign(root, 0, 0.0, twopi, 0.0)

        self.update_all_edges()
        # 清空层级缓存
        if hasattr(self, '_node_level_cache'):
            self._node_level_cache.clear()
        self.push_history("arrange_radial")
        logger.info("完成径向排列")

    @performance_monitor
    @error_handler("树形排列时出错")
    def arrange_tree(self, root=None):
        effective_root = self._get_effective_root_node()
        if not effective_root:
            return
        if root is None or root not in self.graph:
            root = effective_root
        self.set_root_node(root)
        try:
            T = nx.bfs_tree(self.graph, root)
        except nx.NetworkXError:
            root = effective_root
            T = nx.bfs_tree(self.graph, root)

        children = defaultdict(list)
        for u, v in T.edges():
            children[u].append(v)
        for k in children:
            children[k].sort(key=lambda s: s.lower())

        # 使用用户设置的参数作为间距
        x_spacing = self.TARGET_EDGE
        y_spacing = self.TARGET_EDGE * 0.9
        pos = {}
        order = 0

        def dfs(n, depth=0):
            nonlocal order
            ch = children.get(n, [])
            if not ch:
                pos[n] = (order * x_spacing, depth * y_spacing)
                order += 1
            else:
                for c in ch:
                    dfs(c, depth + 1)
                xs = [pos[c][0] for c in ch]
                pos[n] = (sum(xs) / len(xs), depth * y_spacing)

        dfs(root, 0)

        center = self.view.mapToScene(self.view.viewport().rect().center())
        if pos:
            xs = [p[0] for p in pos.values()]
            ys = [p[1] for p in pos.values()]
            cx = (min(xs) + max(xs)) / 2
            cy = (min(ys) + max(ys)) / 2
            for n, (x, y) in pos.items():
                self._set_node_pos(n, self._snap(QPointF(center.x() + (x - cx), center.y() + (y - cy))))
        else:
            self._set_node_pos(root, self._snap(center))

        self.update_all_edges()
        # 清空层级缓存
        if hasattr(self, '_node_level_cache'):
            self._node_level_cache.clear()
        self.push_history("arrange_tree")
        logger.info("完成树形排列")

    def _set_node_pos(self, n, p: QPointF):
        if n in self.nodes:
            self.nodes[n].setPos(p)
            if self.graph.has_node(n):
                self.graph.nodes[n]['pos'] = (p.x(), p.y())
            try:
                if hasattr(self, '_spatial'):
                    old = self._pos_cache.get(n, (self.nodes[n].x(), self.nodes[n].y()))
                    self._spatial.move(n, old[0], old[1], p.x(), p.y())
                self._pos_cache[n] = (p.x(), p.y())
            except Exception:
                pass

    def snapshot(self):
        self._sync_graph_from_scene()
        data = nx.node_link_data(self.graph, edges="links")
        selected = self.selected_node.name if self.selected_node else None
        return {"data": data, "selected": selected, "root_node": self.root_node_name}

    def load_snapshot(self, snap):
        try:
            g = nx.node_link_graph(snap["data"], edges="links") if isinstance(snap, dict) else nx.node_link_graph(snap, edges="links")
            self.graph = g
            self.refresh_scene()
            sel = snap.get("selected") if isinstance(snap, dict) else None
            if sel and sel in self.nodes:
                self.select_node(self.nodes[sel])
            if isinstance(snap, dict) and "root_node" in snap and snap["root_node"] in self.nodes:
                self.root_node_name = snap["root_node"]
            elif self.nodes:
                self.root_node_name = list(self.nodes.keys())[-1]
        except Exception as e:
            logger.error(f"加载快照失败: {e}")

    def push_history(self, reason: str = ""):
        """保存历史记录，确保状态一致性"""
        # 确保场景状态与图数据同步
        self._sync_graph_from_scene()
        
        # 当图结构变化时，清空层级缓存
        if reason in ["add_child", "delete", "connect", "disconnect", "import_json", "import_md", "arrange_radial", "arrange_tree"]:
            if hasattr(self, '_node_level_cache'):
                self._node_level_cache.clear()
                
        snap = self.snapshot()
        self.undo_stack.append(snap)
        if len(self.undo_stack) > self.HISTORY_LIMIT:
            self.undo_stack.pop(0)
        self.redo_stack.clear()
        self._autosave_timer.start(150)
        logger.debug(f"历史记录已保存: {reason}")

    def undo(self):
        if len(self.undo_stack) < 2:
            return
        last = self.undo_stack.pop()
        self.redo_stack.append(last)
        prev = self.undo_stack[-1]
        self.load_snapshot(prev)
        self._autosave_timer.start(100)
        logger.debug("执行撤销操作")

    def redo(self):
        if not self.redo_stack:
            return
        s = self.redo_stack.pop()
        self.undo_stack.append(s)
        self.load_snapshot(s)
        self._autosave_timer.start(100)
        logger.debug("执行重做操作")

    def autosave(self):
        try:
            self._sync_graph_from_scene()
            data = nx.node_link_data(self.graph, edges="links")
            Path(AUTOSAVE_PATH).write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding='utf-8')
            logger.debug("自动保存完成")
        except Exception as e:
            logger.error(f"自动保存失败: {e}")

    @error_handler("刷新场景时出错")
    def refresh_scene(self):
        """安全的场景刷新"""
        try:
            current_selection = self.selected_node.name if self.selected_node else None
            
            if hasattr(self, 'scene'):
                for node in list(self.nodes.values()):
                    try:
                        # 安全断开连接
                        node.moved.disconnect()
                        node.color_changed.disconnect()
                        node.renamed.disconnect()
                    except (TypeError, RuntimeError) as e:
                        logger.debug(f"断开节点信号失败（可能已断开）: {e}")
                        
                self.scene.clear()
                self.scene.edges_by_node.clear()
                
            self.nodes.clear()
            self.edges.clear()

            if not self.graph.nodes:
                self.root_node_name = None
                self.refresh_node_list()
                return

            for name, attrs in self.graph.nodes(data=True):
                color = hex_to_qcolor(attrs.get('color', "#7EC8E3"))
                # 从运行期默认值获取新节点的样式
                try:
                    rdefs = self.get_runtime_defaults()
                except Exception:
                    rdefs = {}
                node_item = MindMapNode(
                    name,
                    color,
                    font_size=int(rdefs.get('NODE_FONT_SIZE', getattr(self, 'NODE_FONT_SIZE', 12))),
                    pad_x=int(rdefs.get('NODE_PADDING_X', getattr(self, 'NODE_PADDING_X', 8))),
                    pad_y=int(rdefs.get('NODE_PADDING_Y', getattr(self, 'NODE_PADDING_Y', 6))),
                    corner_radius=int(rdefs.get('NODE_CORNER_RADIUS', getattr(self, 'NODE_CORNER_RADIUS', 12)))
                )
                node_item.moved.connect(self._on_node_moved)
                node_item.color_changed.connect(lambda _ni, n=name: self._on_node_color_changed(n))
                node_item.renamed.connect(self._on_node_renamed)
                x, y = attrs.get('pos', (0.0, 0.0))
                node_item.setPos(float(x), float(y))
                self.scene.addItem(node_item)
                self.nodes[name] = node_item

            for u, v in self.graph.edges:
                if u in self.nodes and v in self.nodes:
                    self.create_edge(self.nodes[u], self.nodes[v])

            if self.root_node_name is None and self.nodes:
                self.root_node_name = list(self.nodes.keys())[0]
                
            if current_selection and current_selection in self.nodes:
                self.select_node(self.nodes[current_selection])

            self.refresh_node_list()
            logger.info("场景刷新完成")
            
        except Exception as e:
            logger.error(f"刷新场景失败: {e}")
            if hasattr(self, 'scene'):
                self.scene.clear()
            self.nodes.clear()
            self.edges.clear()

# ---------------------------- 大纲数据结构 ----------------------------

# ------------------------------------------------------------------
# 1) Model：数据结构
# ------------------------------------------------------------------

@dataclass
class OutlineNode:
    """纯数据节点。与 Qt 解耦，便于测试与复用。"""
    title: str
    children: List["OutlineNode"] = field(default_factory=list)

    def to_dict(self) -> dict:
        """递归序列化为 JSON 友好的 dict。"""
        return {"title": self.title, "children": [c.to_dict() for c in self.children]}

    @staticmethod
    def from_dict(d: dict) -> "OutlineNode":
        n = OutlineNode(d.get("title", ""))
        for c in d.get("children", []):
            n.children.append(OutlineNode.from_dict(c))
        return n

# ------------------------------------------------------------------
# 2) Model <-> 文本/JSON 的编解码（纯逻辑，无 Qt 依赖）
# ------------------------------------------------------------------
class OutlineCodec:
    """负责把“缩进文本/JSON”与 OutlineNode 树互转的工具集合。"""
    BULLET_PREFIXES = ["- ", "* ", "+ "]
    @staticmethod
    def _expand_tabs(s: str, tab_size: int = 4) -> str:
        return s.expandtabs(tab_size)

    @staticmethod
    def _leading_spaces(s: str) -> int:
        """获取行首空格数。仅以空格决定层级（制表符已被展开）。"""
        return len(s) - len(s.lstrip(" "))

    @staticmethod
    def _strip_bullet(s: str) -> str:
        """
        去掉常见项目符号或编号：
        - 符号：- / * / + 后跟空格
        - 编号：1. / 2) / 3、 等
        """
        s = s.lstrip()
        for p in BULLET_PREFIXES:
            if s.startswith(p):
                return s[len(p):].strip()
        m = re.match(r"^\d+[\.\)、]\s*", s)
        if m:
            return s[m.end():].strip()
        return s.strip()

    @staticmethod
    def _infer_indent_unit(lines: Iterable[str]) -> int:
        """
        推断缩进单位：统计所有非空行的空格数，取相邻差值的最大公约数。
        这样可容忍“手工缩进不完全一致”的文本。
        """
        indents = []
        for raw in lines:
            if not raw.strip():
                continue
            s = OutlineCodec._expand_tabs(raw)
            n = OutlineCodec._leading_spaces(s)
            if n > 0:
                indents.append(n)
        if not indents:
            return INDENT_SPACES
        diffs, si = [], sorted(indents)
        for i in range(1, len(si)):
            d = si[i] - si[i - 1]
            if d > 0:
                diffs.append(d)
        if not diffs:
            return INDENT_SPACES
        from math import gcd
        g = diffs[0]
        for d in diffs[1:]:
            g = gcd(g, d)
        return max(1, min(g, 8))

    @staticmethod
    def parse_outline(outline_text: str) -> OutlineNode:
        """
        将“缩进文本”（可带 -/*/+ 或编号）解析为 OutlineNode 树。
        - 空行 / 空标题 行会被跳过，避免“空节点”。
        """
        lines = outline_text.splitlines()
        unit = OutlineCodec._infer_indent_unit(lines)
        root = OutlineNode("ROOT")
        stack: List[Tuple[int, OutlineNode]] = [(-1, root)]
        for raw in lines:
            if not raw.strip():
                continue
            s = OutlineCodec._expand_tabs(raw)
            level = OutlineCodec._leading_spaces(s) // unit
            title = OutlineCodec._strip_bullet(s)
            if not title:  # 跳过空标题
                continue
            node = OutlineNode(title=title)
            while stack and stack[-1][0] >= level:
                stack.pop()
            stack[-1][1].children.append(node)
            stack.append((level, node))
        return root

    @staticmethod
    def render_markdown(root: OutlineNode, bullet: str = "- ", indent_spaces: int = INDENT_SPACES) -> str:
        """
        将 OutlineNode 树渲染为“缩进风格的文本”。
        - bullet="- " => 标准 Markdown 列表
        - bullet=""   => 非标准（仅空格缩进）
        """
        def dfs(n: OutlineNode, depth: int, out: List[str]):
            for c in n.children:
                line = " " * (depth * indent_spaces) + (bullet + c.title if bullet else c.title)
                out.append(line)
                dfs(c, depth + 1, out)
        buf: List[str] = []
        dfs(root, 0, buf)
        return "\n".join(buf)


# ------------------------------------------------------------------
# 3) 自定义视图与代理（处理内联编辑时的“回写抖动”）
# ------------------------------------------------------------------

class MindTree(QTreeWidget):
    """在原生 QTreeWidget 基础上，加一个结构变更信号（用于拖拽后通知）。"""
    structureChanged = pyqtSignal()
    def dropEvent(self, event):
        super().dropEvent(event)
        self.structureChanged.emit()

class TitleDelegate(QStyledItemDelegate):
    """
    控制“树上内联编辑”的编辑器创建/销毁，
    以便在编辑期间告诉 MainWindow：
      - 当前正处于 item 编辑（_in_item_edit=True）
      - 当前是哪一个 item（_editing_item=...）
      这样 update_labels() 就能跳过这个 item 的 setText，避免光标跳动。
    """
    def __init__(self, owner, *args, **kwargs):
        super().__init__(*args, **kwargs); self.owner = owner

    def createEditor(self, parent, option, index):
        editor = super().createEditor(parent, option, index)
        self.owner._in_item_edit = True
        try:
            item = self.owner.tree.itemFromIndex(index)
        except Exception:
            item = None
        self.owner._editing_item = item
        self.owner._suppress_editor_sync = True  # 编辑中禁止回写左侧编辑器
        return editor

    def destroyEditor(self, editor, index):
        super().destroyEditor(editor, index)
        self.owner._in_item_edit = False
        self.owner._editing_item = None
        self.owner._suppress_editor_sync = False

    def setEditorData(self, editor, index):
        """进入编辑时，展示“原始标题”（不带自动编号）。"""
        raw = index.data(TITLE_ROLE)
        if raw:
            editor.setText(raw)
        else:
            super().setEditorData(editor, index)

    def setModelData(self, editor, model, index):
        """保存编辑结果时，去掉用户误打的前置编号。"""
        text = re.sub(r"^\d+(?:\.\d+)*\s+", "", editor.text()).strip()
        model.setData(index, text, TITLE_ROLE)
        model.setData(index, text, Qt.DisplayRole)

# ------------------------------------------------------------------
# 4) MainWindow（控制/同步层）
# ------------------------------------------------------------------

def pick_first_available(candidates, families, fallback):
    s = set(families)
    for c in candidates:
        if c in s:
            return c
    return fallback

class OutlineViewWindow(QMainWindow):
    def __init__(self, parent=None):  # 修改这里，添加parent参数
        super().__init__(parent) 
        self.settings = QSettings("LolStudio", "OutlineMindmapPresetsPlus")
        self._init_toolbar_and_menu()
        self.setWindowTitle("大纲思维导图")
        self.resize(1500, 1000)


        # ---- 视图状态 ----
        self.show_numbers: bool = self.settings.value("show_numbers", True, type=bool)
        self.color_levels: bool = self.settings.value("color_levels", True, type=bool)
        self.accent_name: str = self.settings.value("accent_name", "彩虹", type=str)
        self.accent = ACCENTS.get(self.accent_name, "#ff6b6b")
        self.theme_name: str = self.settings.value("theme_name", "极简", type=str)
        self.search_term: str = ""

        # ---- 同步状态保护 ----
        self._suppress_editor_sync: bool = False   # 来自编辑器的变更期间，不把树回写到编辑器
        self._in_item_edit: bool = False           # 树正在内联编辑
        self._editing_item: Optional[QTreeWidgetItem] = None

        # ---- 粘贴板（结构级复制/剪切） ----
        self.node_clipboard: Optional[dict] = None
        self.clipboard_cut: bool = False

        # ---- 节流重建 ----
        self.debounce_timer = QTimer(self); self.debounce_timer.setSingleShot(True)
        self.debounce_timer.timeout.connect(self._rebuild_tree_due_to_editor)

        # ---- 字体初始化 ----
        families = QFontDatabase().families()
        ui_default = self.settings.value(
            "ui_font",
            pick_first_available(["PingFang SC","Microsoft YaHei","Source Han Sans SC","Noto Sans CJK SC"],
                                 families, self.font().family())
        )
        tree_default = self.settings.value("tree_font", ui_default)
        mono_default = self.settings.value(
            "mono_font",
            pick_first_available(["JetBrains Mono","Cascadia Code","Fira Code","Consolas","Menlo","Monaco"],
                                 families, QFontDatabase.systemFont(QFontDatabase.FixedFont).family())
        )
        font_size_default = int(self.settings.value("font_size", 15))

        # ---- 主布局 ----
        splitter = QSplitter(Qt.Horizontal, self); self.splitter = splitter
        left, right = QWidget(self), QWidget(self)
        splitter.addWidget(left); splitter.addWidget(right)
        self.setCentralWidget(splitter)
        splitter.setSizes([780, 660])

        # 左侧：纯文本编辑器（只负责“原始大纲文本”，不含编号）
        self.editor = QTextEdit(self)
        self.editor.setPlaceholderText("在此编写大纲（缩进=层级；可写 -/*/+ 或编号；也可直接空格缩进）")
        self.editor.setLineWrapMode(QTextEdit.NoWrap)
        self.editor.setAcceptRichText(False)     # 禁止富文本粘贴，避免带入异常字符
        self.editor.textChanged.connect(self._on_editor_text_changed)

        left_layout = QVBoxLayout(left); left_layout.setContentsMargins(18,18,18,18)
        left_layout.addWidget(self.editor, 1)

        # 右侧：树（交互视图）
        self.tree = MindTree(self)
        self.tree.setHeaderHidden(True)
        self.tree.setAlternatingRowColors(True)
        self.tree.setIndentation(24)
        self.tree.setAnimated(True)
        self.tree.setExpandsOnDoubleClick(True)
        self.tree.setSelectionMode(QAbstractItemView.SingleSelection)
        self.tree.setDragEnabled(True)
        self.tree.setAcceptDrops(True)
        self.tree.setDropIndicatorShown(True)
        self.tree.setDragDropMode(QAbstractItemView.InternalMove)
        self.tree.structureChanged.connect(self.after_tree_changed)

        # 内联编辑代理：负责“正在编辑项”的状态标记
        self.tree.setItemDelegateForColumn(0, TitleDelegate(self))

        # 右键菜单 & 事件过滤（快捷键/空白双击新增）
        self.tree.installEventFilter(self)
        self.tree.viewport().installEventFilter(self)
        self.tree.itemChanged.connect(self.on_item_changed)
        self.tree.setContextMenuPolicy(Qt.CustomContextMenu)
        self.tree.customContextMenuRequested.connect(self.open_context_menu)

        right_layout = QVBoxLayout(right); right_layout.setContentsMargins(18,18,18,18)
        right_layout.addWidget(self.tree, 1)

        # 状态栏
        self.setStatusBar(QStatusBar(self))

        # 文本初始化（从上次退出时恢复）
        last_text = self.settings.value("outline_text", "", type=str)
        if last_text.strip():
            self.editor.setText(last_text)
        else:
            self.editor.setText(
                "项目纲要\n"
                "  背景与目标\n"
                "  关键用户\n"
                "    核心用户\n"
                "    次级用户\n"
                "  功能列表\n"
                "    功能 A\n"
                "    功能 B\n"
                "  里程碑\n"
                "    M1 原型\n"
                "    M2 内测\n"
                "    M3 发布\n"
            )

        # 应用字体/样式并首次构建树
        self.ui_font = QFont(ui_default, pointSize=font_size_default)
        self.tree_font = QFont(tree_default, pointSize=font_size_default)
        self.mono_font = QFont(mono_default, pointSize=font_size_default)
        self.apply_fonts()
        self.apply_styles()
        self.rebuild_tree_from_text()
        self._init_shortcuts()

        # 恢复窗口几何与分栏
        geo = self.settings.value("window_geometry")
        if isinstance(geo, QByteArray): self.restoreGeometry(geo)
        state = self.settings.value("splitter_state")
        if isinstance(state, QByteArray): splitter.restoreState(state)
        splitter.splitterMoved.connect(lambda *_: self.defer_persist())

        self.statusBar().showMessage("提示：F1 查看快捷键；Tab/Shift+Tab 缩进/反缩进。")

    # -------------- 外观 --------------

    def apply_styles(self):
        """根据主题与点缀色刷新样式表与调色板。"""
        accent = self.accent; theme = self.theme_name

        if theme == "极简":
            window_bg = "#ffffff"; panel_bg = "#ffffff"; alt_bg = "#f6f7fb"; text = "#222222"; border = "#eaeaea"
        elif theme == "马卡龙":
            window_bg = ("qlineargradient(x1:0,y1:0, x2:1,y2:1, stop:0 #fff1f2, stop:0.33 #ecfeff, stop:0.66 #f0fdf4, stop:1 #fdf4ff)")
            panel_bg = ("qlineargradient(x1:0,y1:0, x2:0,y2:1, stop:0 #ffffff, stop:1 #fff7fb)")
            alt_bg = "#fef2f2"; text = "#1f2937"; border = "#f5d0fe"
        elif theme == "霓虹":
            window_bg = ("qlineargradient(x1:0,y1:0, x2:1,y2:1, stop:0 #090a0f, stop:1 #0b1220)")
            panel_bg = ("qlineargradient(x1:0,y1:0, x2:0,y2:1, stop:0 #0b0f19, stop:1 #0f172a)")
            alt_bg = "#101827"; text = "#e5f2ff"; border = "#222639"
        elif theme == "多彩":
            window_bg = ("qlineargradient(x1:0,y1:0, x2:1,y2:1, stop:0 #fdf2f8, stop:0.25 #eff6ff, stop:0.5 #ecfeff, stop:0.75 #f0fdf4, stop:1 #fff7ed)")
            panel_bg = ("qlineargradient(x1:0,y1:0, x2:0,y2:1, stop:0 #ffffff, stop:1 #fafafa)")
            alt_bg = "#f1f5f9"; text = "#111111"; border = "#e5e7eb"
        elif theme == "浅色":
            window_bg = "#ffffff"; panel_bg = "#ffffff"; alt_bg = "#f3f4f6"; text = "#111111"; border = "#e5e7eb"
        elif theme == "炭黑":
            window_bg = "#0b1220"; panel_bg = "#0f172a"; alt_bg = "#111827"; text = "#e5e7eb"; border = "#1f2937"
        else:  # 纯黑
            window_bg = "#000000"; panel_bg = "#000000"; alt_bg = "#0a0a0a"; text = "#e5e7eb"; border = "#1f1f1f"

        is_rainbow = (self.accent_name == "彩虹")
        menu_bg = ("qlineargradient(x1:0,y1:0, x2:1,y2:0, stop:0 #f59e0b, stop:0.16 #ef4444, stop:0.33 #8b5cf6, stop:0.5 #06b6d4, stop:0.66 #10b981, stop:0.83 #22c55e, stop:1 #3b82f6)"
                   if is_rainbow or theme in ("马卡龙","多彩","霓虹") else panel_bg)

        self.setStyleSheet(f"""
            QMainWindow {{ background: {window_bg}; }}
            QWidget {{ color:{text}; }}
            QTextEdit, QTreeWidget {{ background:{panel_bg}; border:1px solid {border}; border-radius:12px; }}
            QTextEdit:focus, QTreeWidget:focus {{ border:1px solid {accent}; }}
            QTreeView::item {{ padding:8px 6px; }}
            QTreeView::item:selected {{ background:{accent}33; color:{text}; }}
            QTreeView {{ alternate-background-color: {alt_bg}; }}
            QStatusBar {{ background:{panel_bg}; border-top:1px solid {border}; }}
            QMenu {{ background: {menu_bg}; border: 1px solid {border}; border-radius: 10px; padding: 6px; }}
            QMenu::separator {{ height: 1px; margin: 6px 8px; background: {accent}; }}
            QMenu::item {{ padding: 6px 14px; background: transparent; }}
            QMenu::item:selected {{ background: {accent}55; border-radius: 6px; }}
        """)

        pal = self.palette()
        pal.setColor(QPalette.AlternateBase, QColor(alt_bg if not theme=="马卡龙" else "#fce7f3"))
        pal.setColor(QPalette.Highlight, QColor(accent))
        pal.setColor(QPalette.HighlightedText, QColor(text))
        self.setPalette(pal)

        self.apply_search(self.search_term)

    def apply_fonts(self):
        """统一设置三处字体：UI / 树 / 等宽编辑器。"""
        self.setFont(self.ui_font)
        self.tree.setFont(self.tree_font)
        self.editor.setFont(self.mono_font)
        self.defer_persist()

    def change_accent(self, name: str):
        self.accent_name = name; self.accent = ACCENTS.get(name, "#ff6b6b")
        self.apply_styles(); self.defer_persist()

    def change_theme(self, name: str):
        self.theme_name = name; self.apply_styles(); self.defer_persist()

    # -------------- 新增同步思维导图和大纲视图 --------------
    def sync_from_mindmap(self):
        """从思维导图同步数据到大纲视图"""
        try:
            # 获取父窗口（MindMapApp实例）
            parent_app = self.parent()
            if not parent_app or not hasattr(parent_app, 'graph'):
                logger.warning("无法连接到思维导图主窗口")
                return
                
            # 获取思维导图数据
            graph = parent_app.graph
            if not graph.nodes:
                # 思维导图为空，清空编辑器
                self.editor.clear()
                return
                
            # 构建大纲文本
            outline_text = self._convert_graph_to_outline(graph, parent_app.root_node_name)
            
            # 更新编辑器内容
            self.editor.blockSignals(True)
            self.editor.setPlainText(outline_text)
            self.editor.blockSignals(False)
            
            # 重建树
            self.rebuild_tree_from_text()
            
            logger.info("从思维导图同步数据完成")
            
        except Exception as e:
            logger.error(f"同步思维导图数据失败: {e}")
            QMessageBox.warning(self, "同步失败", f"无法从思维导图同步数据: {e}")

    def _convert_graph_to_outline(self, graph, root_node_name):
        """将网络图转换为大纲文本格式"""
        if not root_node_name or root_node_name not in graph:
            # 如果没有有效根节点，使用第一个节点
            root_node_name = list(graph.nodes())[0] if graph.nodes else ""
            
        if not root_node_name:
            return ""
            
        # 使用BFS遍历图，构建层级结构
        visited = set()
        node_levels = {}
        node_children = {}
        
        # BFS遍历
        queue = [(root_node_name, 0)]
        visited.add(root_node_name)
        node_levels[root_node_name] = 0
        
        while queue:
            current_node, level = queue.pop(0)
            
            # 获取邻居节点（子节点）
            neighbors = list(graph.neighbors(current_node))
            # 排除已经访问过的节点（避免循环）
            unvisited_neighbors = [n for n in neighbors if n not in visited]
            
            node_children[current_node] = unvisited_neighbors
            
            for neighbor in unvisited_neighbors:
                visited.add(neighbor)
                node_levels[neighbor] = level + 1
                queue.append((neighbor, level + 1))
        
        # 构建大纲文本
        lines = []
        
        def add_node_to_outline(node, depth):
            indent = " " * (depth * INDENT_SPACES)
            lines.append(f"{indent}- {node}")
            
            # 递归添加子节点
            for child in node_children.get(node, []):
                add_node_to_outline(child, depth + 1)
        
        # 从根节点开始构建
        add_node_to_outline(root_node_name, 0)
        
        return "\n".join(lines)
    # -------------- 快捷键 --------------

    def _init_shortcuts(self):
        self.addAction(self._mk_action("Ctrl+F", self.prompt_search))
        self.addAction(self._mk_action("F3", lambda: self.find_next(False)))
        self.addAction(self._mk_action("Shift+F3", lambda: self.find_next(True)))
        self.addAction(self._mk_action("Ctrl+E", self.expand_all))
        self.addAction(self._mk_action("Ctrl+Shift+E", self.collapse_all))
        self.addAction(self._mk_action("Ctrl+N", self.shortcut_new_sibling_or_top))
        self.addAction(self._mk_action("Ctrl+Shift+N", lambda: self.add_child(self.tree.currentItem()) if self.tree.currentItem() else self.add_top_level()))
        self.addAction(self._mk_action("Ctrl+T", self.add_top_level))
        self.addAction(self._mk_action("Ctrl+Up", lambda: self.move_up(self.tree.currentItem())))
        self.addAction(self._mk_action("Ctrl+Down", lambda: self.move_down(self.tree.currentItem())))
        self.addAction(self._mk_action("Ctrl+D", lambda: self.duplicate_item(self.tree.currentItem())))
        self.addAction(self._mk_action("F1", self.show_shortcuts_dialog))


        # === 仅认 Ctrl + Key_Plus / Ctrl + Key_Minus ===
        self.sc_zoom_in_main = QShortcut(QKeySequence(Qt.CTRL | Qt.Key_Plus), self)
        self.sc_zoom_in_main.activated.connect(lambda: self.adjust_font_size(+1))

        self.sc_zoom_out_main = QShortcut(QKeySequence(Qt.CTRL | Qt.Key_Minus), self)
        self.sc_zoom_out_main.activated.connect(lambda: self.adjust_font_size(-1))

        # （可选）数字小键盘的 + / -，带 KeypadModifier，避免误判
        self.sc_zoom_in_numpad = QShortcut(QKeySequence(Qt.CTRL | Qt.KeypadModifier | Qt.Key_Plus), self)
        self.sc_zoom_in_numpad.activated.connect(lambda: self.adjust_font_size(+1))

        self.sc_zoom_out_numpad = QShortcut(QKeySequence(Qt.CTRL | Qt.KeypadModifier | Qt.Key_Minus), self)
        self.sc_zoom_out_numpad.activated.connect(lambda: self.adjust_font_size(-1))

    def _mk_action(self, shortcut, fn):
        act = QAction(self); act.setShortcut(shortcut); act.triggered.connect(fn); return act

    def shortcut_new_sibling_or_top(self):
        it = self.tree.currentItem()
        if it: self.add_sibling(it)
        else: self.add_top_level()

    def adjust_font_size(self, delta: int):
        size = max(10, min(28, self.ui_font.pointSize() + delta))
        self.ui_font.setPointSize(size); self.tree_font.setPointSize(size); self.mono_font.setPointSize(size)
        self.apply_fonts()

    def prompt_search(self):
        term, ok = QInputDialog.getText(self, "搜索", "输入关键词（回车确认）：", text=self.search_term)
        if ok:
            self.search_term = term; self.apply_search(self.search_term)

    # -------------- 树构建/刷新 --------------

    def rebuild_tree_from_text(self):
        """从左侧编辑器文本重建右侧树。"""
        text = self.editor.toPlainText()
        self.defer_persist()
        root = OutlineCodec.parse_outline(text)

        # 批量更新期间不触发 itemChanged
        self.tree.blockSignals(True)
        self.tree.clear()

        def add_children(parent_item: QTreeWidgetItem, node: OutlineNode, depth: int):
            for child in node.children:
                it = QTreeWidgetItem()
                it.setData(0, TITLE_ROLE, child.title)
                it.setData(0, DEPTH_ROLE, depth)
                it.setText(0, child.title)  # 初始显示=原始标题（update_labels 后会合成编号）
                it.setFlags(it.flags() | Qt.ItemIsEditable | Qt.ItemIsEnabled |
                            Qt.ItemIsSelectable | Qt.ItemIsDragEnabled | Qt.ItemIsDropEnabled)
                parent_item.addChild(it)
                if child.children:
                    add_children(it, child, depth + 1)

        dummy = QTreeWidgetItem(self.tree)
        add_children(dummy, root, 1)
        while dummy.childCount() > 0:
            self.tree.addTopLevelItem(dummy.takeChild(0))
        self.tree.takeTopLevelItem(self.tree.indexOfTopLevelItem(dummy))

        self.tree.expandAll()
        self.tree.blockSignals(False)

        self.update_labels()
        self.apply_search(self.search_term)

    def _rebuild_tree_due_to_editor(self):
        """仅当“来自编辑器”的变更节流触发时调用：期间禁止回写编辑器。"""
        try:
            self._suppress_editor_sync = True
            self.rebuild_tree_from_text()
        finally:
            self._suppress_editor_sync = False

    def _apply_item_color(self, item: QTreeWidgetItem, depth: int):
        if not self.color_levels:
            item.setForeground(0, QColor("#111827")); return
        palette = LEVEL_COLORS_LIGHT; color = QColor(palette[depth % len(palette)])
        item.setForeground(0, color)

    def recompute_depths(self):
        """当树结构变化后，重新标注每个节点的深度（用于配色）。"""
        def walk(item: QTreeWidgetItem, depth: int):
            item.setData(0, DEPTH_ROLE, depth)
            for i in range(item.childCount()):
                walk(item.child(i), depth + 1)
        for i in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(i), 1)

    def update_labels(self):
        """
        根据“当前编号策略”刷新右侧树上的显示文本。
        - 注意：如果某项正在内联编辑，跳过它的 setText，避免光标跳动。
        """
        self.tree.blockSignals(True)

        def path_number(item: QTreeWidgetItem) -> str:
            """计算类似 2.3.5 的“路径编号”。"""
            parts, cur = [], item
            while cur is not None and cur.parent() is not None:
                idx = cur.parent().indexOfChild(cur) + 1
                parts.append(str(idx))
                cur = cur.parent()
            if cur is not None and cur.parent() is None:
                idx = self.tree.indexOfTopLevelItem(cur) + 1
                parts.append(str(idx))
            return ".".join(reversed(parts)) if parts else ""

        def walk(item: QTreeWidgetItem):
            title = item.data(0, TITLE_ROLE) or item.text(0)
            label = f"{path_number(item)} {title}" if self.show_numbers else title
            if not (self._in_item_edit and self._editing_item is item):
                item.setText(0, label)
            d = int(item.data(0, DEPTH_ROLE) or 1)
            self._apply_item_color(item, d)
            for i in range(item.childCount()):
                walk(item.child(i))

        for i in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(i))

        self.tree.blockSignals(False)

    # -------------- 搜索（仅改样式，不改文本） --------------

    def apply_search(self, term: str):
        term = (term or "").strip().lower()
        hl = QColor(self.accent); hl.setAlpha(48 if self.theme_name in ("多彩", "浅色", "极简", "马卡龙") else 90)

        if not term:
            # 清空搜索：恢复展开 + 清除样式
            def clear_styles(it: QTreeWidgetItem):
                it.setBackground(0, self.tree.palette().base())
                f = it.font(0); f.setBold(False); it.setFont(0, f)
                it.setExpanded(True)
                for i in range(it.childCount()):
                    clear_styles(it.child(i))
            for i in range(self.tree.topLevelItemCount()):
                clear_styles(self.tree.topLevelItem(i))
            return

        def walk(item: QTreeWidgetItem) -> bool:
            raw = (item.data(0, TITLE_ROLE) or item.text(0))
            matched = term in raw.lower()
            # 重置样式
            item.setBackground(0, self.tree.palette().base())
            f = item.font(0); f.setBold(False); item.setFont(0, f)
            child_has = False
            for i in range(item.childCount()):
                if walk(item.child(i)): child_has = True
            if matched:
                item.setBackground(0, hl)
                f = item.font(0); f.setBold(True); item.setFont(0, f)
            item.setExpanded(matched or child_has)
            return matched or child_has

        for i in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(i))

    def all_items_preorder(self) -> List[QTreeWidgetItem]:
        items: List[QTreeWidgetItem] = []
        def walk(it: QTreeWidgetItem):
            items.append(it)
            for i in range(it.childCount()):
                walk(it.child(i))
        for i in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(i))
        return items

    def find_next(self, backwards=False):
        term = (self.search_term or "").strip().lower()
        if not term:
            return
        items = self.all_items_preorder()
        matches = [i for i in items if term in ((i.data(0, TITLE_ROLE) or i.text(0)).lower())]
        if not matches:
            return
        cur = self.tree.currentItem()
        if cur not in matches:
            target = matches[-1] if backwards else matches[0]
        else:
            idx = matches.index(cur)
            target = matches[idx-1] if backwards else matches[(idx+1) % len(matches)]
        self.tree.setCurrentItem(target)
        p = target.parent()
        while p:
            p.setExpanded(True); p = p.parent()
        self.tree.scrollToItem(target)
        f = target.font(0); f.setBold(True); target.setFont(0, f)

    # -------------- 右键菜单与动作 --------------

    def _add_action(self, menu: QMenu, text_with_hint: str, slot, shortcut: Optional[str]=None):
        act = QAction(text_with_hint, self)
        if shortcut: act.setShortcut(QKeySequence(shortcut))
        act.triggered.connect(slot); menu.addAction(act); return act

    def open_context_menu(self, pos: QPoint):
        item = self.tree.itemAt(pos); menu = QMenu(self)

        # 文件
        m_file = menu.addMenu("文件")
        self._add_action(m_file, "打开…\tCtrl+O", self.open_outline, "Ctrl+O")
        self._add_action(m_file, "保存…\tCtrl+S", self.save_outline, "Ctrl+S")
        m_file.addSeparator()
        self._add_action(m_file, "导出 Markdown（可选标准/非标准）", self.export_markdown)
        self._add_action(m_file, "导出 JSON", self.export_json)


        # 视图
        m_view = menu.addMenu("视图")
        self._add_action(m_view, "展开全部\tCtrl+E", self.expand_all, "Ctrl+E")
        self._add_action(m_view, "折叠全部\tCtrl+Shift+E", self.collapse_all, "Ctrl+Shift+E")
        m_view.addSeparator()
        a_num = QAction("显示编号 1.1.1", self); a_num.setCheckable(True); a_num.setChecked(self.show_numbers)
        a_num.toggled.connect(lambda v: self.toggle_numbers(Qt.Checked if v else Qt.Unchecked)); m_view.addAction(a_num)
        a_color = QAction("层级配色", self); a_color.setCheckable(True); a_color.setChecked(self.color_levels)
        a_color.toggled.connect(lambda v: self.toggle_colors(Qt.Checked if v else Qt.Unchecked)); m_view.addAction(a_color)

        # 搜索
        m_search = menu.addMenu("搜索")
        self._add_action(m_search, "输入关键词…\tCtrl+F", self.prompt_search, "Ctrl+F")
        self._add_action(m_search, "下一处\tF3", lambda: self.find_next(False), "F3")
        self._add_action(m_search, "上一处\tShift+F3", lambda: self.find_next(True), "Shift+F3")
        self._add_action(m_search, "清除搜索", lambda: (setattr(self, "search_term", ""), self.apply_search("")))

        menu.addSeparator()

        # 节点
        if item:
            m_node = menu.addMenu("节点")
            self._add_action(m_node, "新增同级\tCtrl+N", lambda: self.add_sibling(item), "Ctrl+N")
            self._add_action(m_node, "新增子级\tCtrl+Shift+N", lambda: self.add_child(item), "Ctrl+Shift+N")
            self._add_action(m_node, "重命名\tF2", lambda: self.rename_item(item), "F2")
            self._add_action(m_node, "删除\tDelete", lambda: self.delete_item(item), "Delete")
            m_node.addSeparator()
            self._add_action(m_node, "缩进（Tab）\tTab", lambda: self.indent_item(item))
            self._add_action(m_node, "反缩进（Shift+Tab）\tShift+Tab", lambda: self.outdent_item(item))
            m_node.addSeparator()
            self._add_action(m_node, "上移\tCtrl+↑", lambda: self.move_up(item), "Ctrl+Up")
            self._add_action(m_node, "下移\tCtrl+↓", lambda: self.move_down(item), "Ctrl+Down")
            m_node.addSeparator()
            self._add_action(m_node, "复制\tCtrl+C", lambda: self.copy_item(item), "Ctrl+C")
            self._add_action(m_node, "剪切\tCtrl+X", lambda: self.cut_item(item), "Ctrl+X")
            self._add_action(m_node, "粘贴为子级\tCtrl+V", lambda: self.paste_to_child(item), "Ctrl+V")
        else:
            self._add_action(menu, "新增顶级节点\tCtrl+T", self.add_top_level, "Ctrl+T")
            self._add_action(menu, "粘贴为顶级", self.paste_as_top)

        menu.addSeparator()
        self._add_action(menu, "快捷键说明…\tF1", self.show_shortcuts_dialog)

        menu.exec_(self.tree.viewport().mapToGlobal(pos))

    # -------------- 事件过滤：空白双击新增 + 热键处理 --------------

    def eventFilter(self, obj, event):
        if obj is self.tree.viewport() and event.type() == QEvent.MouseButtonDblClick:
            if self.tree.itemAt(event.pos()) is None:
                self.add_top_level(); return True

        if obj is self.tree and event.type() == QEvent.KeyPress:
            key = event.key(); mods = event.modifiers(); item = self.tree.currentItem()

            if key in (Qt.Key_Return, Qt.Key_Enter):
                if item is None: self.add_top_level()
                elif mods & Qt.ControlModifier: self.add_child(item)
                elif mods & Qt.ShiftModifier: self.add_sibling(item)
                else: self.rename_item(item)
                return True

            if key == Qt.Key_Tab and mods == Qt.NoModifier and item:
                self.indent_item(item); return True
            if key in (Qt.Key_Backtab, Qt.Key_Tab) and (mods & Qt.ShiftModifier) and item:
                self.outdent_item(item); return True

            if key == Qt.Key_F2 and item: self.rename_item(item); return True
            if key == Qt.Key_Delete and item: self.delete_item(item); return True

            if key == Qt.Key_N and (mods & Qt.ControlModifier):
                if item and not (mods & Qt.ShiftModifier): self.add_sibling(item)
                elif item and (mods & Qt.ShiftModifier): self.add_child(item)
                else: self.add_top_level()
                return True

            if key == Qt.Key_T and (mods & Qt.ControlModifier): self.add_top_level(); return True
            if key == Qt.Key_Up and (mods & Qt.ControlModifier) and item: self.move_up(item); return True
            if key == Qt.Key_Down and (mods & Qt.ControlModifier) and item: self.move_down(item); return True

            if key == Qt.Key_C and (mods & Qt.ControlModifier) and item: self.copy_item(item); return True
            if key == Qt.Key_X and (mods & Qt.ControlModifier) and item: self.cut_item(item); return True
            if key == Qt.Key_V and (mods & Qt.ControlModifier):
                if item: self.paste_to_child(item)
                else: self.paste_as_top()
                return True

            if key == Qt.Key_D and (mods & Qt.ControlModifier) and item: self.duplicate_item(item); return True

            if key == Qt.Key_F3 and not (mods & Qt.ShiftModifier): self.find_next(False); return True
            if key == Qt.Key_F3 and (mods & Qt.ShiftModifier): self.find_next(True); return True
            if key == Qt.Key_F1: self.show_shortcuts_dialog(); return True

        return super().eventFilter(obj, event)

    # -------------- 节点增删改与同步回写 --------------

    def _new_item(self, title="新节点") -> QTreeWidgetItem:
        it = QTreeWidgetItem()
        it.setData(0, TITLE_ROLE, title)
        it.setText(0, title)
        it.setFlags(it.flags() | Qt.ItemIsEditable | Qt.ItemIsEnabled |
                    Qt.ItemIsSelectable | Qt.ItemIsDragEnabled | Qt.ItemIsDropEnabled)
        return it

    def add_top_level(self):
        it = self._new_item(); self.tree.addTopLevelItem(it); it.setData(0, DEPTH_ROLE, 1)
        self.after_tree_changed(edit_item=it)

    def add_sibling(self, item: QTreeWidgetItem):
        if not item: return self.add_top_level()
        parent = item.parent(); it = self._new_item()
        if parent:
            idx = parent.indexOfChild(item); parent.insertChild(idx + 1, it)
            it.setData(0, DEPTH_ROLE, int(item.data(0, DEPTH_ROLE) or 1))
        else:
            idx = self.tree.indexOfTopLevelItem(item); self.tree.insertTopLevelItem(idx + 1, it)
            it.setData(0, DEPTH_ROLE, 1)
        self.after_tree_changed(edit_item=it)

    def add_child(self, item: QTreeWidgetItem):
        if not item: return self.add_top_level()
        it = self._new_item(); item.addChild(it)
        it.setData(0, DEPTH_ROLE, int(item.data(0, DEPTH_ROLE) or 1) + 1)
        item.setExpanded(True); self.after_tree_changed(edit_item=it)

    def rename_item(self, item: QTreeWidgetItem):
        raw = item.data(0, TITLE_ROLE) or ""
        self.tree.blockSignals(True); item.setText(0, raw); self.tree.blockSignals(False)
        self.tree.editItem(item, 0)

    def delete_item(self, item: QTreeWidgetItem):
        if not item: return
        if QMessageBox.question(self, "删除节点", "确定删除该节点及其所有子节点？",
                                QMessageBox.Yes|QMessageBox.No) != QMessageBox.Yes:
            return
        parent = item.parent()
        if parent: parent.removeChild(item)
        else: self.tree.takeTopLevelItem(self.tree.indexOfTopLevelItem(item))
        self.after_tree_changed()

    def move_up(self, item: QTreeWidgetItem):
        if not item: return
        parent = item.parent()
        if parent:
            idx = parent.indexOfChild(item)
            if idx > 0:
                parent.takeChild(idx); parent.insertChild(idx - 1, item); self.after_tree_changed()
        else:
            idx = self.tree.indexOfTopLevelItem(item)
            if idx > 0:
                self.tree.takeTopLevelItem(idx); self.tree.insertTopLevelItem(idx - 1, item); self.after_tree_changed()

    def move_down(self, item: QTreeWidgetItem):
        if not item: return
        parent = item.parent()
        if parent:
            idx = parent.indexOfChild(item)
            if idx < parent.childCount() - 1:
                parent.takeChild(idx); parent.insertChild(idx + 1, item); self.after_tree_changed()
        else:
            idx = self.tree.indexOfTopLevelItem(item)
            if idx < self.tree.topLevelItemCount() - 1:
                self.tree.takeTopLevelItem(idx); self.tree.insertTopLevelItem(idx + 1, item); self.after_tree_changed()

    def indent_item(self, item: QTreeWidgetItem):
        """缩进：成为前一个同级项的子节点。"""
        if not item: return
        parent = item.parent()
        if parent:
            idx = parent.indexOfChild(item)
            if idx <= 0:
                self.statusBar().showMessage("无法继续缩进：前面没有同级节点。", 2000); return
            prev_sibling = parent.child(idx - 1)
            parent.takeChild(idx); prev_sibling.addChild(item); prev_sibling.setExpanded(True)
        else:
            idx = self.tree.indexOfTopLevelItem(item)
            if idx <= 0:
                self.statusBar().showMessage("无法继续缩进：前面没有顶级同级节点。", 2000); return
            prev_top = self.tree.topLevelItem(idx - 1)
            self.tree.takeTopLevelItem(idx); prev_top.addChild(item); prev_top.setExpanded(True)
        self.after_tree_changed()

    def outdent_item(self, item: QTreeWidgetItem):
        """反缩进：上移一层，成为父节点之后的同级项。"""
        if not item: return
        parent = item.parent()
        if not parent:
            self.statusBar().showMessage("已是顶级节点，无法反缩进。", 2000); return
        grand = parent.parent()
        if grand:
            idx_parent = grand.indexOfChild(parent); parent.removeChild(item); grand.insertChild(idx_parent + 1, item)
        else:
            idx_parent = self.tree.indexOfTopLevelItem(parent); parent.removeChild(item)
            self.tree.insertTopLevelItem(idx_parent + 1, item)
        self.after_tree_changed()

    def duplicate_item(self, item: QTreeWidgetItem):
        if not item: return
        copy_dict = self.item_to_dict(item)
        new_item = self.dict_to_item(copy_dict)
        parent = item.parent()
        if parent:
            idx = parent.indexOfChild(item); parent.insertChild(idx + 1, new_item)
        else:
            idx = self.tree.indexOfTopLevelItem(item); self.tree.insertTopLevelItem(idx + 1, new_item)
        self.after_tree_changed(edit_item=new_item)

    def copy_item(self, item: QTreeWidgetItem):
        self.node_clipboard = self.item_to_dict(item); self.clipboard_cut = False
        self.statusBar().showMessage("已复制节点", 1500)

    def cut_item(self, item: QTreeWidgetItem):
        self.node_clipboard = self.item_to_dict(item); self.clipboard_cut = True
        parent = item.parent()
        if parent: parent.removeChild(item)
        else: self.tree.takeTopLevelItem(self.tree.indexOfTopLevelItem(item))
        self.after_tree_changed(); self.statusBar().showMessage("已剪切节点，粘贴以完成移动", 2000)

    def paste_to_child(self, item: QTreeWidgetItem):
        if not self.node_clipboard: return
        new_item = self.dict_to_item(self.node_clipboard); item.addChild(new_item); item.setExpanded(True)
        self.after_tree_changed(edit_item=new_item)
        if self.clipboard_cut: self.node_clipboard = None; self.clipboard_cut = False

    def paste_as_top(self):
        if not self.node_clipboard: return
        new_item = self.dict_to_item(self.node_clipboard); self.tree.addTopLevelItem(new_item)
        new_item.setData(0, DEPTH_ROLE, 1)
        self.after_tree_changed(edit_item=new_item)
        if self.clipboard_cut: self.node_clipboard = None; self.clipboard_cut = False

    # -------------- 导入/导出 --------------

    def item_to_dict(self, item: QTreeWidgetItem) -> dict:
        d = {"title": item.data(0, TITLE_ROLE) or item.text(0), "children": []}
        for i in range(item.childCount()):
            d["children"].append(self.item_to_dict(item.child(i)))
        return d

    def dict_to_item(self, d: dict) -> QTreeWidgetItem:
        it = self._new_item(d.get("title",""))
        for c in d.get("children", []):
            it.addChild(self.dict_to_item(c))
        return it

    def export_markdown(self):
        """整棵树导出为 Markdown（可选标准/非标准）。"""
        options = ["标准 Markdown 列表（以 - 开头）", "非标准（仅空格缩进，无 - ）"]
        choice, ok = QInputDialog.getItem(self, "导出 Markdown 格式", "选择格式：", options, 0, False)
        if not ok: return
        bullet = "- " if choice.startswith("标准") else ""
        text = self.tree_to_markdown(bullet=bullet)
        default_name = "outline.md" if bullet else "outline.txt"
        path, _ = QFileDialog.getSaveFileName(
            self, "导出 Markdown", default_name, "Markdown/Text (*.md *.txt);;All Files (*)"
        )
        if not path: return
        try:
            with io.open(path, "w", encoding="utf-8") as f: f.write(text)
            self.statusBar().showMessage("已导出", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出失败：{e}")

    def export_json(self):
        """整棵树导出为 JSON。"""
        if self.tree.topLevelItemCount() == 1:
            root_obj = self.item_to_dict(self.tree.topLevelItem(0))
        else:
            root_obj = {"title": "Mindmap", "children": [
                self.item_to_dict(self.tree.topLevelItem(i)) for i in range(self.tree.topLevelItemCount())
            ]}
        text = json.dumps(root_obj, ensure_ascii=False, indent=2)
        path, _ = QFileDialog.getSaveFileName(self, "导出 JSON", "outline.json", "JSON (*.json);;All Files (*)")
        if not path: return
        try:
            with io.open(path, "w", encoding="utf-8") as f: f.write(text)
            self.statusBar().showMessage("已导出 JSON", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出失败：{e}")

    def export_current_branch_markdown(self):
        """将当前选中的分支导出为 Markdown（可选标准/非标准）。"""
        item = self.tree.currentItem()
        if not item:
            QMessageBox.information(self, "提示", "请先选择一个节点（将导出该节点及子树）。"); return
        options = ["标准 Markdown 列表（以 - 开头）", "非标准（仅空格缩进，无 - ）"]
        choice, ok = QInputDialog.getItem(self, "导出当前分支", "选择格式：", options, 0, False)
        if not ok: return
        bullet = "- " if choice.startswith("标准") else ""
        text = self.branch_to_markdown(item, bullet=bullet)
        default_name = "branch.md" if bullet else "branch.txt"
        path, _ = QFileDialog.getSaveFileName(self, "导出当前分支", default_name, "Markdown/Text (*.md *.txt);;All Files (*)")
        if not path: return
        try:
            with io.open(path, "w", encoding="utf-8") as f: f.write(text)
            self.statusBar().showMessage("已导出当前分支", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出失败：{e}")

    def export_current_branch_json(self):
        item = self.tree.currentItem()
        if not item:
            QMessageBox.information(self, "提示", "请先选择一个节点（将导出该节点及子树）。"); return
        text = json.dumps(self.item_to_dict(item), ensure_ascii=False, indent=2)
        path, _ = QFileDialog.getSaveFileName(self, "导出当前分支为 JSON", "branch.json", "JSON (*.json)")
        if not path: return
        try:
            with io.open(path, "w", encoding="utf-8") as f: f.write(text)
            self.statusBar().showMessage("已导出当前分支", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"导出失败：{e}")

    def branch_to_markdown(self, item: QTreeWidgetItem, bullet: str = "- ") -> str:
        """从任意树项出发，序列化为（子）大纲文本。"""
        def walk(it, depth, out: List[str]):
            title = it.data(0, TITLE_ROLE) or it.text(0)
            if not title: return
            out.append(" " * ((depth - 1) * INDENT_SPACES) + (bullet + title if bullet else title))
            for i in range(it.childCount()):
                walk(it.child(i), depth + 1, out)
        lines: List[str] = []; walk(item, 1, lines); return "\n".join(lines)

    def open_outline(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "打开大纲", "", "Markdown/Text/JSON (*.md *.txt *.json);;All Files (*)"
        )
        if not path: return
        try:
            if path.lower().endswith(".json"):
                with io.open(path, "r", encoding="utf-8", errors="ignore") as f:
                    obj = json.load(f)
                if isinstance(obj, dict) and "children" in obj:
                    root = OutlineNode.from_dict(obj)
                    # 读取 JSON 后把树渲染成“非标准大纲文本”（无 - ，更利于左侧编辑）
                    md = OutlineCodec.render_markdown(root, bullet="", indent_spaces=INDENT_SPACES)
                    self.editor.setText(md)
                else:
                    QMessageBox.warning(self, "提示", "JSON 结构不符合期望（需包含 title 与 children）。")
            else:
                with io.open(path, "r", encoding="utf-8", errors="ignore") as f:
                    self.editor.setText(f.read())
            self.statusBar().showMessage(f"已打开：{os.path.basename(path)}", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"打开失败：{e}")

    def save_outline(self):
        path, _ = QFileDialog.getSaveFileName(
            self, "保存大纲为…", "outline.txt", "Markdown/Text (*.md *.txt);;All Files (*)"
        )
        if not path: return
        try:
            with io.open(path, "w", encoding="utf-8") as f: f.write(self.editor.toPlainText())
            self.statusBar().showMessage(f"已保存：{os.path.basename(path)}", 3000)
        except Exception as e:
            QMessageBox.critical(self, "错误", f"保存失败：{e}")

    # -------------- 添加工具栏与菜单 --------------

    def _init_toolbar_and_menu(self):
        # ---- 1) 创建动作（QAction） ----
        self.act_open   = QAction(QIcon.fromTheme("document-open"),   "打开", self)
        self.act_save   = QAction(QIcon.fromTheme("document-save"),   "保存 TXT", self)
        self.act_exp_md = QAction(QIcon.fromTheme("document-export"), "导出 Markdown", self)
        self.act_exp_js = QAction(QIcon.fromTheme("document-export"), "导出 JSON", self)


        # 快捷键（和你现有的保持一致/互补）
        self.act_open.setShortcut("Ctrl+O")
        self.act_save.setShortcut("Ctrl+S")

        # 绑定槽函数（直接复用你现有的方法）
        self.act_open.triggered.connect(self.open_outline)
        self.act_save.triggered.connect(self.save_outline)
        self.act_exp_md.triggered.connect(self.export_markdown)
        self.act_exp_js.triggered.connect(self.export_json)


        # ---- 2) 工具栏（按钮）----
        tb = self.addToolBar("文件")
        tb.setMovable(True)
        tb.addAction(self.act_open)
        tb.addAction(self.act_save)
        tb.addSeparator()
        tb.addAction(self.act_exp_md)
        tb.addAction(self.act_exp_js)
        tb.addSeparator()


        # ---- 3) 菜单栏（可选，但很实用）----
        mb = self.menuBar()
        m_file = mb.addMenu("文件")
        m_file.addAction(self.act_open)
        m_file.addAction(self.act_save)
        m_file.addSeparator()
        m_file.addAction(self.act_exp_md)
        m_file.addAction(self.act_exp_js)
        m_file.addSeparator()


    # -------------- 编辑器<->树 的同步 --------------

    def tree_to_markdown(self, bullet: str = "- ") -> str:
        """整棵树 -> 文本（用于导出或同步回编辑器）。"""
        def walk(item: QTreeWidgetItem, depth: int, out: List[str]):
            title = item.data(0, TITLE_ROLE) or item.text(0)
            if not title:  # 不输出空标题
                return
            out.append(" " * ((depth - 1) * INDENT_SPACES) + (bullet + title if bullet else title))
            for i in range(item.childCount()):
                walk(item.child(i), depth + 1, out)
        lines: List[str] = []
        for i in range(self.tree.topLevelItemCount()):
            walk(self.tree.topLevelItem(i), 1, lines)
        return "\n".join(lines)

    def sync_editor_from_tree(self):
        """当结构变化（来自右侧）时，把树序列化回编辑器。"""
        if self._suppress_editor_sync:
            return  # 正在由编辑器触发的更新或内联编辑，暂不回写（避免光标跳动）
        md = self.tree_to_markdown(bullet="")  # 左侧保持“非标准大纲文本”（无 - ）
        self.editor.blockSignals(True)
        self.editor.setText(md)
        self.editor.blockSignals(False)

    def _on_editor_text_changed(self):
        """编辑器内容变化：节流重建树，并短暂禁止回写编辑器。"""
        self._suppress_editor_sync = True
        self.debounce_timer.start(DEBOUNCE_MS_EDITOR_TO_TREE)

    # -------------- 切换项 --------------

    def toggle_numbers(self, state):
        self.show_numbers = (state == Qt.Checked or state is True)
        self.update_labels(); self.defer_persist()

    def toggle_colors(self, state):
        self.color_levels = (state == Qt.Checked or state is True)
        self.update_labels(); self.defer_persist()

    def expand_all(self): self.tree.expandAll()
    def collapse_all(self): self.tree.collapseAll()

    # -------------- 变更回调（来自树的编辑） --------------

    def on_item_changed(self, item: QTreeWidgetItem, column: int):
        """
        树项文本被用户修改：
        - 清理前置编号
        - 若标题为空 => 删除节点（杜绝“数字占位”）
        - 然后刷新编号并同步回编辑器
        """
        new_text = re.sub(r"^\d+(?:\.\d+)*\s+", "", item.text(0)).strip()
        if not new_text:
            self.tree.blockSignals(True)
            parent = item.parent()
            if parent: parent.removeChild(item)
            else:
                idx = self.tree.indexOfTopLevelItem(item)
                if idx >= 0: self.tree.takeTopLevelItem(idx)
            self.tree.blockSignals(False)
            self.after_tree_changed()
            return

        item.setData(0, TITLE_ROLE, new_text)
        self.update_labels()
        self.sync_editor_from_tree()
        self.defer_persist()

    def after_tree_changed(self, edit_item: Optional[QTreeWidgetItem] = None):
        """树结构变化后的统一收尾：重算深度、刷新标签、可选聚焦编辑、同步回编辑器。"""
        self.recompute_depths()
        self.update_labels()
        if edit_item:
            self.tree.setCurrentItem(edit_item); self.rename_item(edit_item)
        self.sync_editor_from_tree()
        self.defer_persist()

    # -------------- 偏好持久化 --------------

    def defer_persist(self):
        if not hasattr(self, "save_timer") or self.save_timer is None:
            self.save_timer = QTimer(self); self.save_timer.setSingleShot(True)
            self.save_timer.timeout.connect(self.persist_preferences)
        self.save_timer.start(300)

    def persist_preferences(self):
        self.settings.setValue("ui_font", self.ui_font.family())
        self.settings.setValue("tree_font", self.tree_font.family())
        self.settings.setValue("mono_font", self.mono_font.family())
        self.settings.setValue("font_size", self.ui_font.pointSize())
        self.settings.setValue("show_numbers", self.show_numbers)
        self.settings.setValue("color_levels", self.color_levels)
        self.settings.setValue("accent_name", self.accent_name)
        self.settings.setValue("theme_name", self.theme_name)
        self.settings.setValue("outline_text", self.editor.toPlainText())
        self.settings.setValue("window_geometry", self.saveGeometry())
        if isinstance(self.centralWidget(), QSplitter):
            self.settings.setValue("splitter_state", self.splitter.saveState())

    def closeEvent(self, event):
        self.persist_preferences()
        super().closeEvent(event)

    # -------------- 帮助 --------------

    def show_shortcuts_dialog(self):
        text = (
            "【大纲思维导图 · 快捷键一览】\n"
            "—— 编辑/结构 ——\n"
            "  Enter         ：重命名（无选中则新建顶级；Ctrl+Enter 新建子级；Shift+Enter 新建同级）\n"
            "  Tab           ：缩进（作为上一同级的子节点）\n"
            "  Shift+Tab     ：反缩进（上移一层，位于父节点之后）\n"
            "  Ctrl+N        ：新增同级（无选中则顶级）\n"
            "  Ctrl+Shift+N  ：新增子级（无选中则顶级）\n"
            "  Ctrl+T        ：新增顶级\n"
            "  Delete        ：删除所选节点/子树\n"
            "  Ctrl+↑/↓      ：上移/下移\n"
            "  Ctrl+C / X / V：复制 / 剪切 / 粘贴为子级\n"
            "  Ctrl+D        ：克隆\n"
            "  Ctrl+O        ：打开文档\n"
            "  Ctrl+S        ：保存为txt\n"
            "\n"
            "—— 查找/视图 ——\n"
            "  Ctrl+F        ：输入关键词\n"
            "  F3 / Shift+F3 ：下一个 / 上一个匹配\n"
            "  Ctrl+E        ：展开全部\n"
            "  Ctrl+Shift+E  ：折叠全部\n"
            "  Ctrl+= / Ctrl+-：字号放大/缩小\n"
            "  F1            ：打开此说明\n"
        )
        QMessageBox.information(self, "快捷键说明", text)

# ---------------------------- 主程序入口 ------------------------------
def main():
    try:
        app = QApplication(sys.argv)
        window = MindMapApp()
        window.show()
        logger.info("应用启动成功")
        sys.exit(app.exec_())
    except Exception as e:
        logger.critical(f"应用启动失败: {e}")
        raise

if __name__ == "__main__":
    main()
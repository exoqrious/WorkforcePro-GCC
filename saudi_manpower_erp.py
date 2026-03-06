#!/usr/bin/env python3
"""
Saudi Manpower ERP Platform
============================
A comprehensive, production-ready Enterprise Resource Planning system
specifically designed for Saudi Arabian manpower and staffing companies.

Features:
- Complete HR & Payroll Management with Saudi Labor Law compliance
- GOSI calculation (Saudi and non-Saudi rates)
- EOSB (End of Service Benefit) calculation
- WPS (Wage Protection System) SIF file generation
- ZATCA-compliant e-invoicing with TLV QR codes
- Full Accounting with Chart of Accounts
- Contract and Client management
- Leave management
- Asset management
- Financial reporting (P&L, Balance Sheet, Trial Balance)
- PySide6 modern GUI with Arabic support

Author: Saudi Manpower ERP Team
Version: 2.0.0
License: Commercial
"""

# =============================================================================
# SECTION 1: IMPORTS AND CONSTANTS
# =============================================================================

import sys
import os
import re
import json
import math
import base64
import struct
import hashlib
import logging
import sqlite3
import datetime
import calendar
import threading
import traceback
import io
import csv
import time
import uuid
import copy
import textwrap
import string
import random
import tempfile
import shutil
import subprocess
import platform
from pathlib import Path
from typing import Optional, List, Dict, Any, Tuple, Union, Callable
from functools import partial, lru_cache
from contextlib import contextmanager
from dataclasses import dataclass, field, asdict
from enum import Enum, IntEnum
from collections import defaultdict, OrderedDict
from decimal import Decimal, ROUND_HALF_UP

# Third-party imports
try:
    import bcrypt
    HAS_BCRYPT = True
except ImportError:
    HAS_BCRYPT = False
    logging.warning("bcrypt not available, using SHA-256 fallback")

try:
    import pandas as pd
    HAS_PANDAS = True
except ImportError:
    HAS_PANDAS = False

try:
    import numpy as np
    HAS_NUMPY = True
except ImportError:
    HAS_NUMPY = False

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    import matplotlib.dates as mdates
    from matplotlib.backends.backend_agg import FigureCanvasAgg
    from matplotlib.figure import Figure
    HAS_MATPLOTLIB = True
except ImportError:
    HAS_MATPLOTLIB = False

try:
    import qrcode
    HAS_QRCODE = True
except ImportError:
    HAS_QRCODE = False

try:
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib.units import cm, mm, inch
    from reportlab.lib.enums import TA_LEFT, TA_CENTER, TA_RIGHT
    from reportlab.platypus import (
        SimpleDocTemplate, Table, TableStyle, Paragraph, Spacer,
        Image as RLImage, PageBreak, HRFlowable, KeepTogether
    )
    from reportlab.pdfgen import canvas as rl_canvas
    from reportlab.graphics.shapes import Drawing, Rect, String
    HAS_REPORTLAB = True
except ImportError:
    HAS_REPORTLAB = False

try:
    import openpyxl
    from openpyxl.styles import (
        Font, PatternFill, Alignment, Border, Side, numbers
    )
    from openpyxl.utils import get_column_letter
    from openpyxl.chart import BarChart, PieChart, LineChart, Reference
    HAS_OPENPYXL = True
except ImportError:
    HAS_OPENPYXL = False

try:
    from PIL import Image as PILImage
    HAS_PIL = True
except ImportError:
    HAS_PIL = False

try:
    from dateutil.relativedelta import relativedelta
    from dateutil.parser import parse as date_parse
    HAS_DATEUTIL = True
except ImportError:
    HAS_DATEUTIL = False

# PySide6 imports
try:
    from PySide6.QtWidgets import (
        QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
        QGridLayout, QFormLayout, QStackedWidget, QSplitter,
        QLabel, QPushButton, QLineEdit, QTextEdit, QPlainTextEdit,
        QComboBox, QSpinBox, QDoubleSpinBox, QCheckBox, QRadioButton,
        QTabWidget, QTableWidget, QTableWidgetItem, QTreeWidget,
        QTreeWidgetItem, QListWidget, QListWidgetItem, QHeaderView,
        QScrollArea, QFrame, QGroupBox, QProgressBar, QSlider,
        QDateEdit, QTimeEdit, QDateTimeEdit, QCalendarWidget,
        QDialog, QDialogButtonBox, QFileDialog, QMessageBox,
        QInputDialog, QColorDialog, QFontDialog, QProgressDialog,
        QSizePolicy, QToolBar, QStatusBar, QMenuBar, QMenu,
        QSystemTrayIcon, QDockWidget, QAction, QToolButton,
        QAbstractItemView, QButtonGroup, QStackedLayout,
        QScrollBar, QSplashScreen
    )
    from PySide6.QtCore import (
        Qt, QTimer, QThread, QObject, Signal, Slot, QRunnable,
        QThreadPool, QSize, QPoint, QRect, QDate, QDateTime,
        QTime, QUrl, QSettings, QTranslator, QLocale,
        QAbstractTableModel, QModelIndex, QSortFilterProxyModel,
        QRegularExpression, QPropertyAnimation, QEasingCurve,
        QParallelAnimationGroup, QSequentialAnimationGroup,
        QEvent, QMimeData
    )
    from PySide6.QtGui import (
        QFont, QFontMetrics, QIcon, QPixmap, QImage, QColor,
        QPainter, QPen, QBrush, QLinearGradient, QRadialGradient,
        QPainterPath, QKeySequence, QAction as QGuiAction,
        QCursor, QTextDocument, QTextCursor, QValidator,
        QIntValidator, QDoubleValidator, QRegularExpressionValidator,
        QPalette, QShortcut, QStandardItemModel, QStandardItem
    )
    HAS_PYSIDE6 = True
except ImportError:
    HAS_PYSIDE6 = False
    print("ERROR: PySide6 not installed. Run: pip install PySide6")
    sys.exit(1)

# =============================================================================
# CONSTANTS
# =============================================================================

APP_NAME = "Saudi Manpower ERP"
APP_VERSION = "2.0.0"
APP_AUTHOR = "WorkforcePro GCC"
APP_COPYRIGHT = f"© {datetime.datetime.now().year} {APP_AUTHOR}"
APP_WEBSITE = "https://workforcepro.com.sa"

# Database
DB_PATH = Path.home() / ".saudi_manpower_erp" / "erp.db"
DB_VERSION = 10

# Company defaults
DEFAULT_COMPANY_NAME = "Saudi Manpower Company"
DEFAULT_COMPANY_NAME_AR = "شركة القوى العاملة السعودية"
DEFAULT_COUNTRY = "Saudi Arabia"
DEFAULT_CURRENCY = "SAR"
DEFAULT_VAT_RATE = 0.15  # 15% VAT in Saudi Arabia
DEFAULT_TIMEZONE = "Asia/Riyadh"

# GOSI Rates
GOSI_SAUDI_EMPLOYER_RATE = 0.0975    # 9.75%
GOSI_SAUDI_EMPLOYEE_RATE = 0.0975    # 9.75%
GOSI_NON_SAUDI_EMPLOYER_RATE = 0.02  # 2.00% (work hazard only)
GOSI_NON_SAUDI_EMPLOYEE_RATE = 0.00  # 0%
GOSI_SALARY_CEILING = 45000          # SAR 45,000 max GOSI base

# Annual leave per Saudi Labor Law
ANNUAL_LEAVE_DAYS = 21  # First 5 years
ANNUAL_LEAVE_DAYS_SENIOR = 30  # After 5 years

# EOSB per Saudi Labor Law
EOSB_HALF_MONTH_YEARS = 5   # First 5 years: 0.5 month per year
EOSB_FULL_MONTH_START = 5   # After 5 years: 1 month per year

# Logging configuration
LOG_DIR = Path.home() / ".saudi_manpower_erp" / "logs"
LOG_FILE = LOG_DIR / f"erp_{datetime.date.today().strftime('%Y%m%d')}.log"

# UI Constants
SIDEBAR_WIDTH = 240
HEADER_HEIGHT = 60
STATUS_BAR_HEIGHT = 25
ICON_SIZE = 20
TABLE_ROW_HEIGHT = 36
ANIMATION_DURATION = 200

# Pagination
DEFAULT_PAGE_SIZE = 50
MAX_PAGE_SIZE = 200

# File paths
ASSETS_DIR = Path(__file__).parent / "assets"
TEMP_DIR = Path(tempfile.gettempdir()) / "saudi_erp"

# Ensure directories exist
DB_PATH.parent.mkdir(parents=True, exist_ok=True)
LOG_DIR.mkdir(parents=True, exist_ok=True)
TEMP_DIR.mkdir(parents=True, exist_ok=True)

# =============================================================================
# LOGGING SETUP
# =============================================================================

def setup_logging():
    """Configure application-wide logging."""
    formatter = logging.Formatter(
        '%(asctime)s [%(levelname)s] %(name)s:%(lineno)d - %(message)s',
        datefmt='%Y-%m-%d %H:%M:%S'
    )

    # File handler
    file_handler = logging.FileHandler(LOG_FILE, encoding='utf-8')
    file_handler.setLevel(logging.DEBUG)
    file_handler.setFormatter(formatter)

    # Console handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)

    # Root logger
    root_logger = logging.getLogger()
    root_logger.setLevel(logging.DEBUG)
    root_logger.addHandler(file_handler)
    root_logger.addHandler(console_handler)

    return logging.getLogger(APP_NAME)

logger = setup_logging()

# =============================================================================
# SECTION 2: CORE FRAMEWORK LAYER
# =============================================================================

class Config:
    """
    Configuration manager for the ERP system.
    Manages settings with defaults, persistence, and type conversion.
    """

    DEFAULTS = {
        "app.language": "en",
        "app.theme": "light",
        "app.font_size": 10,
        "app.show_toolbar": True,
        "app.show_statusbar": True,
        "db.path": str(DB_PATH),
        "db.backup_enabled": True,
        "db.backup_interval_days": 7,
        "company.name": DEFAULT_COMPANY_NAME,
        "company.name_ar": DEFAULT_COMPANY_NAME_AR,
        "company.country": DEFAULT_COUNTRY,
        "company.currency": DEFAULT_CURRENCY,
        "company.vat_rate": DEFAULT_VAT_RATE,
        "payroll.gosi_saudi_employer_rate": GOSI_SAUDI_EMPLOYER_RATE,
        "payroll.gosi_saudi_employee_rate": GOSI_SAUDI_EMPLOYEE_RATE,
        "payroll.gosi_non_saudi_employer_rate": GOSI_NON_SAUDI_EMPLOYER_RATE,
        "payroll.gosi_salary_ceiling": GOSI_SALARY_CEILING,
        "payroll.payment_day": 25,
        "payroll.wps_bank_code": "RJHI",
        "leave.annual_days": ANNUAL_LEAVE_DAYS,
        "leave.sick_days": 30,
        "notifications.email_enabled": False,
        "notifications.check_interval_minutes": 5,
        "ui.records_per_page": DEFAULT_PAGE_SIZE,
        "ui.confirm_delete": True,
        "ui.auto_save": True,
    }

    def __init__(self):
        self._settings: Dict[str, Any] = dict(self.DEFAULTS)
        self._qt_settings = QSettings(APP_AUTHOR, APP_NAME)
        self._load_from_qt()

    def _load_from_qt(self):
        """Load settings from Qt persistent storage."""
        for key in self.DEFAULTS:
            qt_val = self._qt_settings.value(key)
            if qt_val is not None:
                self._settings[key] = qt_val

    def get(self, key: str, default: Any = None) -> Any:
        """Get a configuration value."""
        return self._settings.get(key, default if default is not None else self.DEFAULTS.get(key))

    def set(self, key: str, value: Any):
        """Set a configuration value and persist it."""
        self._settings[key] = value
        self._qt_settings.setValue(key, value)
        self._qt_settings.sync()

    def get_bool(self, key: str, default: bool = False) -> bool:
        """Get a boolean configuration value."""
        val = self.get(key, default)
        if isinstance(val, str):
            return val.lower() in ('true', '1', 'yes')
        return bool(val)

    def get_int(self, key: str, default: int = 0) -> int:
        """Get an integer configuration value."""
        try:
            return int(self.get(key, default))
        except (ValueError, TypeError):
            return default

    def get_float(self, key: str, default: float = 0.0) -> float:
        """Get a float configuration value."""
        try:
            return float(self.get(key, default))
        except (ValueError, TypeError):
            return default

    def reset_to_defaults(self):
        """Reset all settings to default values."""
        self._settings = dict(self.DEFAULTS)
        self._qt_settings.clear()

    def export_settings(self) -> dict:
        """Export current settings as dictionary."""
        return dict(self._settings)

    def import_settings(self, settings: dict):
        """Import settings from dictionary."""
        for key, value in settings.items():
            if key in self.DEFAULTS:
                self.set(key, value)


class ServiceContainer:
    """
    Dependency injection container for the ERP system.
    Manages service instances and their dependencies.
    """

    def __init__(self):
        self._services: Dict[str, Any] = {}
        self._factories: Dict[str, Callable] = {}
        self._singletons: Dict[str, Any] = {}

    def register(self, name: str, factory: Callable, singleton: bool = True):
        """Register a service factory."""
        self._factories[name] = factory
        if not singleton:
            return
        # Eager singleton registration
        logger.debug(f"Registered service: {name}")

    def register_instance(self, name: str, instance: Any):
        """Register an existing instance as a service."""
        self._singletons[name] = instance
        logger.debug(f"Registered instance: {name}")

    def get(self, name: str) -> Any:
        """Get a service by name."""
        # Check singleton cache
        if name in self._singletons:
            return self._singletons[name]

        # Create from factory
        if name in self._factories:
            instance = self._factories[name](self)
            self._singletons[name] = instance
            return instance

        raise KeyError(f"Service not found: {name}")

    def has(self, name: str) -> bool:
        """Check if a service is registered."""
        return name in self._singletons or name in self._factories


class ModuleRegistry:
    """
    Registry for ERP modules.
    Manages module registration, dependencies, and lifecycle.
    """

    def __init__(self):
        self._modules: Dict[str, dict] = {}
        self._enabled: set = set()

    def register_module(self, name: str, display_name: str, icon: str,
                        view_class: type, requires_permission: str = None,
                        order: int = 0):
        """Register an ERP module."""
        self._modules[name] = {
            "name": name,
            "display_name": display_name,
            "icon": icon,
            "view_class": view_class,
            "requires_permission": requires_permission,
            "order": order,
            "enabled": True,
        }
        self._enabled.add(name)
        logger.debug(f"Registered module: {name}")

    def get_module(self, name: str) -> dict:
        """Get module configuration."""
        return self._modules.get(name)

    def get_all_modules(self) -> List[dict]:
        """Get all modules sorted by order."""
        return sorted(
            [m for m in self._modules.values() if m["enabled"]],
            key=lambda x: x["order"]
        )

    def enable_module(self, name: str):
        """Enable a module."""
        if name in self._modules:
            self._modules[name]["enabled"] = True
            self._enabled.add(name)

    def disable_module(self, name: str):
        """Disable a module."""
        if name in self._modules:
            self._modules[name]["enabled"] = False
            self._enabled.discard(name)

    def is_enabled(self, name: str) -> bool:
        """Check if a module is enabled."""
        return name in self._enabled


class EventBus:
    """
    Simple event system for inter-module communication.
    Allows modules to communicate without direct coupling.
    """

    def __init__(self):
        self._listeners: Dict[str, List[Callable]] = defaultdict(list)
        self._once_listeners: Dict[str, List[Callable]] = defaultdict(list)

    def on(self, event: str, callback: Callable):
        """Subscribe to an event."""
        self._listeners[event].append(callback)

    def once(self, event: str, callback: Callable):
        """Subscribe to an event, but only trigger once."""
        self._once_listeners[event].append(callback)

    def off(self, event: str, callback: Callable = None):
        """Unsubscribe from an event."""
        if callback is None:
            self._listeners.pop(event, None)
            self._once_listeners.pop(event, None)
        else:
            if event in self._listeners:
                self._listeners[event] = [
                    cb for cb in self._listeners[event] if cb != callback
                ]

    def emit(self, event: str, *args, **kwargs):
        """Emit an event to all subscribers."""
        # Regular listeners
        for callback in self._listeners.get(event, []):
            try:
                callback(*args, **kwargs)
            except Exception as e:
                logger.error(f"Error in event handler for {event}: {e}")

        # Once listeners
        once_callbacks = self._once_listeners.pop(event, [])
        for callback in once_callbacks:
            try:
                callback(*args, **kwargs)
            except Exception as e:
                logger.error(f"Error in once-event handler for {event}: {e}")

    def emit_async(self, event: str, *args, **kwargs):
        """Emit an event asynchronously in a separate thread."""
        thread = threading.Thread(
            target=self.emit, args=(event, *args), kwargs=kwargs, daemon=True
        )
        thread.start()


# Global instances
config = Config()
event_bus = EventBus()
module_registry = ModuleRegistry()
container = ServiceContainer()

# =============================================================================
# SECTION 3: DATABASE ENGINE
# =============================================================================

class DatabaseManager:
    """
    SQLite database manager with WAL mode, migrations, and helper methods.
    Handles all database operations with connection pooling simulation.
    """

    def __init__(self, db_path: str = None):
        self.db_path = str(db_path or DB_PATH)
        self._local = threading.local()
        self._lock = threading.Lock()
        self._version = DB_VERSION
        logger.info(f"Database path: {self.db_path}")
        self._ensure_directory()

    def _ensure_directory(self):
        """Ensure the database directory exists."""
        Path(self.db_path).parent.mkdir(parents=True, exist_ok=True)

    @property
    def conn(self) -> sqlite3.Connection:
        """Get thread-local database connection."""
        if not hasattr(self._local, 'connection') or self._local.connection is None:
            self._local.connection = self._create_connection()
        return self._local.connection

    def _create_connection(self) -> sqlite3.Connection:
        """Create a new database connection with optimal settings."""
        conn = sqlite3.connect(
            self.db_path,
            detect_types=sqlite3.PARSE_DECLTYPES | sqlite3.PARSE_COLNAMES,
            timeout=30,
            check_same_thread=False
        )
        conn.row_factory = sqlite3.Row

        # Enable WAL mode for better concurrency
        conn.execute("PRAGMA journal_mode=WAL")
        conn.execute("PRAGMA synchronous=NORMAL")
        conn.execute("PRAGMA cache_size=10000")
        conn.execute("PRAGMA temp_store=MEMORY")
        conn.execute("PRAGMA mmap_size=268435456")  # 256MB
        conn.execute("PRAGMA foreign_keys=ON")
        conn.execute("PRAGMA auto_vacuum=INCREMENTAL")

        logger.debug(f"Created database connection (thread: {threading.current_thread().name})")
        return conn

    def close(self):
        """Close the thread-local connection."""
        if hasattr(self._local, 'connection') and self._local.connection:
            self._local.connection.close()
            self._local.connection = None

    @contextmanager
    def transaction(self):
        """Context manager for database transactions."""
        conn = self.conn
        try:
            conn.execute("BEGIN")
            yield conn
            conn.execute("COMMIT")
        except Exception as e:
            conn.execute("ROLLBACK")
            logger.error(f"Transaction rolled back: {e}")
            raise

    def execute(self, sql: str, params: tuple = ()) -> sqlite3.Cursor:
        """Execute a SQL statement."""
        try:
            cursor = self.conn.cursor()
            cursor.execute(sql, params)
            self.conn.commit()
            return cursor
        except sqlite3.Error as e:
            logger.error(f"SQL Error: {e}\nSQL: {sql}\nParams: {params}")
            raise

    def execute_many(self, sql: str, params_list: List[tuple]) -> int:
        """Execute a SQL statement with multiple parameter sets."""
        try:
            cursor = self.conn.cursor()
            cursor.executemany(sql, params_list)
            self.conn.commit()
            return cursor.rowcount
        except sqlite3.Error as e:
            logger.error(f"SQL Error (executemany): {e}\nSQL: {sql}")
            raise

    def fetchall(self, sql: str, params: tuple = ()) -> List[dict]:
        """Execute a SELECT and return all rows as dictionaries."""
        try:
            cursor = self.conn.cursor()
            cursor.execute(sql, params)
            rows = cursor.fetchall()
            return [dict(row) for row in rows]
        except sqlite3.Error as e:
            logger.error(f"Fetchall Error: {e}\nSQL: {sql}\nParams: {params}")
            raise

    def fetchone(self, sql: str, params: tuple = ()) -> Optional[dict]:
        """Execute a SELECT and return one row as dictionary."""
        try:
            cursor = self.conn.cursor()
            cursor.execute(sql, params)
            row = cursor.fetchone()
            return dict(row) if row else None
        except sqlite3.Error as e:
            logger.error(f"Fetchone Error: {e}\nSQL: {sql}\nParams: {params}")
            raise

    def fetchscalar(self, sql: str, params: tuple = ()) -> Any:
        """Execute a SELECT and return a single scalar value."""
        row = self.fetchone(sql, params)
        if row:
            return list(row.values())[0]
        return None

    def insert(self, table: str, data: dict) -> int:
        """Insert a record and return the new ID."""
        columns = ', '.join(data.keys())
        placeholders = ', '.join(['?'] * len(data))
        sql = f"INSERT INTO {table} ({columns}) VALUES ({placeholders})"
        cursor = self.execute(sql, tuple(data.values()))
        return cursor.lastrowid

    def update(self, table: str, data: dict, where: str, where_params: tuple = ()) -> int:
        """Update records and return number of affected rows."""
        set_clause = ', '.join([f"{k} = ?" for k in data.keys()])
        sql = f"UPDATE {table} SET {set_clause} WHERE {where}"
        cursor = self.execute(sql, tuple(data.values()) + where_params)
        return cursor.rowcount

    def delete(self, table: str, where: str, where_params: tuple = ()) -> int:
        """Delete records and return number of affected rows."""
        sql = f"DELETE FROM {table} WHERE {where}"
        cursor = self.execute(sql, where_params)
        return cursor.rowcount

    def table_exists(self, table_name: str) -> bool:
        """Check if a table exists."""
        result = self.fetchone(
            "SELECT name FROM sqlite_master WHERE type='table' AND name=?",
            (table_name,)
        )
        return result is not None

    def get_schema_version(self) -> int:
        """Get the current schema version."""
        try:
            result = self.fetchone("SELECT version FROM schema_version ORDER BY id DESC LIMIT 1")
            return result['version'] if result else 0
        except Exception:
            return 0

    def create_tables(self):
        """Create all database tables with proper schemas."""
        logger.info("Creating database tables...")

        tables_sql = [
            # Schema version tracking
            """
            CREATE TABLE IF NOT EXISTS schema_version (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                version INTEGER NOT NULL,
                applied_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                description TEXT
            )
            """,

            # =========================================================
            # COMPANY & ORGANIZATION
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS companies (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL,
                name_ar TEXT,
                cr_number TEXT UNIQUE,
                vat_number TEXT,
                address TEXT,
                address_ar TEXT,
                city TEXT,
                region TEXT,
                country TEXT DEFAULT 'Saudi Arabia',
                postal_code TEXT,
                phone TEXT,
                fax TEXT,
                email TEXT,
                website TEXT,
                logo_path TEXT,
                bank_name TEXT,
                bank_account TEXT,
                bank_iban TEXT,
                bank_swift TEXT,
                currency TEXT DEFAULT 'SAR',
                fiscal_year_start TEXT DEFAULT '01-01',
                default_vat_rate REAL DEFAULT 0.15,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_companies_cr ON companies(cr_number)",

            """
            CREATE TABLE IF NOT EXISTS branches (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                name TEXT NOT NULL,
                name_ar TEXT,
                code TEXT,
                manager_name TEXT,
                address TEXT,
                city TEXT,
                region TEXT,
                phone TEXT,
                email TEXT,
                is_active INTEGER DEFAULT 1,
                is_head_office INTEGER DEFAULT 0,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_branches_company ON branches(company_id)",

            """
            CREATE TABLE IF NOT EXISTS departments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                branch_id INTEGER REFERENCES branches(id),
                parent_id INTEGER REFERENCES departments(id),
                name TEXT NOT NULL,
                name_ar TEXT,
                code TEXT,
                manager_id INTEGER,
                cost_center_id INTEGER,
                description TEXT,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_departments_company ON departments(company_id)",

            """
            CREATE TABLE IF NOT EXISTS cost_centers (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                code TEXT NOT NULL,
                name TEXT NOT NULL,
                name_ar TEXT,
                description TEXT,
                parent_id INTEGER REFERENCES cost_centers(id),
                budget REAL DEFAULT 0,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_cost_centers_company ON cost_centers(company_id)",

            # =========================================================
            # USERS, ROLES, PERMISSIONS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS roles (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                name TEXT NOT NULL UNIQUE,
                display_name TEXT,
                description TEXT,
                is_system INTEGER DEFAULT 0,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS permissions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                code TEXT NOT NULL UNIQUE,
                name TEXT NOT NULL,
                module TEXT NOT NULL,
                action TEXT NOT NULL,
                description TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_permissions_module ON permissions(module)",

            """
            CREATE TABLE IF NOT EXISTS role_permissions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                role_id INTEGER NOT NULL REFERENCES roles(id) ON DELETE CASCADE,
                permission_id INTEGER NOT NULL REFERENCES permissions(id) ON DELETE CASCADE,
                UNIQUE(role_id, permission_id)
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS users (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                username TEXT NOT NULL UNIQUE,
                password_hash TEXT NOT NULL,
                email TEXT,
                full_name TEXT,
                full_name_ar TEXT,
                employee_id INTEGER,
                company_id INTEGER REFERENCES companies(id),
                branch_id INTEGER REFERENCES branches(id),
                department_id INTEGER REFERENCES departments(id),
                is_active INTEGER DEFAULT 1,
                is_admin INTEGER DEFAULT 0,
                must_change_password INTEGER DEFAULT 0,
                last_login TIMESTAMP,
                login_attempts INTEGER DEFAULT 0,
                locked_until TIMESTAMP,
                language TEXT DEFAULT 'en',
                theme TEXT DEFAULT 'light',
                avatar_path TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_users_username ON users(username)",

            """
            CREATE TABLE IF NOT EXISTS user_roles (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL REFERENCES users(id) ON DELETE CASCADE,
                role_id INTEGER NOT NULL REFERENCES roles(id) ON DELETE CASCADE,
                UNIQUE(user_id, role_id)
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS user_sessions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL REFERENCES users(id),
                session_token TEXT NOT NULL,
                ip_address TEXT,
                user_agent TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                expires_at TIMESTAMP,
                is_active INTEGER DEFAULT 1
            )
            """,

            # =========================================================
            # CLIENTS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS clients (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                client_number TEXT UNIQUE,
                name TEXT NOT NULL,
                name_ar TEXT,
                cr_number TEXT,
                vat_number TEXT,
                industry TEXT,
                client_type TEXT DEFAULT 'corporate',
                address TEXT,
                address_ar TEXT,
                city TEXT,
                region TEXT,
                country TEXT DEFAULT 'Saudi Arabia',
                postal_code TEXT,
                phone TEXT,
                fax TEXT,
                email TEXT,
                website TEXT,
                payment_terms INTEGER DEFAULT 30,
                credit_limit REAL DEFAULT 0,
                account_id INTEGER,
                salesperson_id INTEGER REFERENCES users(id),
                status TEXT DEFAULT 'active',
                rating TEXT,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_clients_company ON clients(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_clients_name ON clients(name)",
            "CREATE INDEX IF NOT EXISTS idx_clients_vat ON clients(vat_number)",

            """
            CREATE TABLE IF NOT EXISTS client_contacts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                client_id INTEGER NOT NULL REFERENCES clients(id) ON DELETE CASCADE,
                first_name TEXT NOT NULL,
                last_name TEXT,
                job_title TEXT,
                department TEXT,
                phone TEXT,
                mobile TEXT,
                email TEXT,
                is_primary INTEGER DEFAULT 0,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_client_contacts_client ON client_contacts(client_id)",

            """
            CREATE TABLE IF NOT EXISTS client_statements (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                client_id INTEGER NOT NULL REFERENCES clients(id),
                statement_date DATE NOT NULL,
                opening_balance REAL DEFAULT 0,
                total_invoiced REAL DEFAULT 0,
                total_paid REAL DEFAULT 0,
                closing_balance REAL DEFAULT 0,
                generated_by INTEGER REFERENCES users(id),
                generated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # EMPLOYEES
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS employees (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                emp_number TEXT UNIQUE,
                first_name TEXT NOT NULL,
                last_name TEXT,
                middle_name TEXT,
                arabic_name TEXT,
                nationality TEXT,
                id_type TEXT DEFAULT 'iqama',
                id_number TEXT,
                iqama_number TEXT UNIQUE,
                iqama_expiry DATE,
                iqama_issue_place TEXT,
                passport_number TEXT,
                passport_expiry DATE,
                passport_issue_country TEXT,
                visa_number TEXT,
                visa_type TEXT,
                visa_expiry DATE,
                visa_issue_date DATE,
                border_number TEXT,
                date_of_birth DATE,
                place_of_birth TEXT,
                gender TEXT DEFAULT 'male',
                marital_status TEXT DEFAULT 'single',
                religion TEXT,
                education TEXT,
                education_field TEXT,
                university TEXT,
                graduation_year INTEGER,
                mobile TEXT,
                mobile_2 TEXT,
                email TEXT,
                emergency_contact TEXT,
                emergency_phone TEXT,
                emergency_relation TEXT,
                current_address TEXT,
                permanent_address TEXT,
                hire_date DATE,
                probation_end_date DATE,
                termination_date DATE,
                termination_reason TEXT,
                rehire_eligible INTEGER DEFAULT 1,
                job_title TEXT,
                job_title_ar TEXT,
                department_id INTEGER REFERENCES departments(id),
                branch_id INTEGER REFERENCES branches(id),
                cost_center_id INTEGER REFERENCES cost_centers(id),
                company_id INTEGER NOT NULL REFERENCES companies(id),
                direct_manager_id INTEGER REFERENCES employees(id),
                employment_type TEXT DEFAULT 'full_time',
                contract_type TEXT DEFAULT 'indefinite',
                work_location TEXT,
                salary_type TEXT DEFAULT 'monthly',
                basic_salary REAL DEFAULT 0,
                housing_allowance REAL DEFAULT 0,
                transport_allowance REAL DEFAULT 0,
                food_allowance REAL DEFAULT 0,
                phone_allowance REAL DEFAULT 0,
                other_allowances REAL DEFAULT 0,
                total_salary REAL DEFAULT 0,
                bank_name TEXT,
                bank_account TEXT,
                bank_iban TEXT,
                bank_swift TEXT,
                payment_method TEXT DEFAULT 'bank_transfer',
                gosi_number TEXT,
                gosi_eligible INTEGER DEFAULT 1,
                gosi_registered_date DATE,
                tax_number TEXT,
                is_saudi INTEGER DEFAULT 0,
                is_active INTEGER DEFAULT 1,
                is_on_leave INTEGER DEFAULT 0,
                notes TEXT,
                photo_path TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_employees_company ON employees(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_employees_emp_number ON employees(emp_number)",
            "CREATE INDEX IF NOT EXISTS idx_employees_department ON employees(department_id)",
            "CREATE INDEX IF NOT EXISTS idx_employees_branch ON employees(branch_id)",
            "CREATE INDEX IF NOT EXISTS idx_employees_iqama ON employees(iqama_number)",
            "CREATE INDEX IF NOT EXISTS idx_employees_active ON employees(is_active)",
            "CREATE INDEX IF NOT EXISTS idx_employees_nationality ON employees(nationality)",

            """
            CREATE TABLE IF NOT EXISTS employee_documents (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id) ON DELETE CASCADE,
                document_type TEXT NOT NULL,
                document_number TEXT,
                issue_date DATE,
                expiry_date DATE,
                issuing_authority TEXT,
                file_path TEXT,
                file_name TEXT,
                file_size INTEGER,
                notes TEXT,
                is_verified INTEGER DEFAULT 0,
                verified_by INTEGER REFERENCES users(id),
                verified_at TIMESTAMP,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_emp_docs_employee ON employee_documents(employee_id)",
            "CREATE INDEX IF NOT EXISTS idx_emp_docs_expiry ON employee_documents(expiry_date)",

            """
            CREATE TABLE IF NOT EXISTS employee_dependents (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id) ON DELETE CASCADE,
                full_name TEXT NOT NULL,
                relationship TEXT NOT NULL,
                date_of_birth DATE,
                nationality TEXT,
                id_number TEXT,
                gender TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS employee_history (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id) ON DELETE CASCADE,
                change_type TEXT NOT NULL,
                field_name TEXT,
                old_value TEXT,
                new_value TEXT,
                effective_date DATE,
                reason TEXT,
                approved_by INTEGER REFERENCES users(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_emp_history_employee ON employee_history(employee_id)",

            """
            CREATE TABLE IF NOT EXISTS employee_assignments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                contract_id INTEGER REFERENCES contracts(id),
                client_id INTEGER REFERENCES clients(id),
                assignment_date DATE,
                end_date DATE,
                bill_rate REAL,
                pay_rate REAL,
                location TEXT,
                position TEXT,
                notes TEXT,
                is_active INTEGER DEFAULT 1,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_emp_assignments_employee ON employee_assignments(employee_id)",

            # =========================================================
            # CONTRACTS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS contracts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                client_id INTEGER NOT NULL REFERENCES clients(id),
                contract_number TEXT UNIQUE,
                title TEXT NOT NULL,
                description TEXT,
                contract_type TEXT DEFAULT 'manpower_supply',
                status TEXT DEFAULT 'draft',
                start_date DATE,
                end_date DATE,
                auto_renew INTEGER DEFAULT 0,
                renewal_period_months INTEGER DEFAULT 12,
                notice_period_days INTEGER DEFAULT 30,
                payment_terms INTEGER DEFAULT 30,
                currency TEXT DEFAULT 'SAR',
                vat_applicable INTEGER DEFAULT 1,
                total_value REAL DEFAULT 0,
                signed_date DATE,
                signed_by TEXT,
                document_path TEXT,
                account_manager_id INTEGER REFERENCES users(id),
                notes TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_contracts_company ON contracts(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_contracts_client ON contracts(client_id)",
            "CREATE INDEX IF NOT EXISTS idx_contracts_status ON contracts(status)",

            """
            CREATE TABLE IF NOT EXISTS contract_lines (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                contract_id INTEGER NOT NULL REFERENCES contracts(id) ON DELETE CASCADE,
                description TEXT NOT NULL,
                quantity REAL DEFAULT 1,
                unit TEXT DEFAULT 'person',
                unit_price REAL DEFAULT 0,
                discount_percent REAL DEFAULT 0,
                total_price REAL DEFAULT 0,
                vat_rate REAL DEFAULT 0.15,
                vat_amount REAL DEFAULT 0,
                line_total REAL DEFAULT 0,
                sort_order INTEGER DEFAULT 0,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_contract_lines_contract ON contract_lines(contract_id)",

            """
            CREATE TABLE IF NOT EXISTS contract_amendments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                contract_id INTEGER NOT NULL REFERENCES contracts(id),
                amendment_number TEXT,
                effective_date DATE,
                description TEXT,
                changes_json TEXT,
                approved_by TEXT,
                document_path TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # PAYROLL
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS payroll_periods (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                period_name TEXT NOT NULL,
                period_year INTEGER NOT NULL,
                period_month INTEGER NOT NULL,
                start_date DATE NOT NULL,
                end_date DATE NOT NULL,
                payment_date DATE,
                status TEXT DEFAULT 'open',
                total_employees INTEGER DEFAULT 0,
                total_gross REAL DEFAULT 0,
                total_deductions REAL DEFAULT 0,
                total_net REAL DEFAULT 0,
                total_gosi_employee REAL DEFAULT 0,
                total_gosi_employer REAL DEFAULT 0,
                closed_by INTEGER REFERENCES users(id),
                closed_at TIMESTAMP,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_payroll_periods_company ON payroll_periods(company_id)",
            "CREATE UNIQUE INDEX IF NOT EXISTS idx_payroll_periods_unique ON payroll_periods(company_id, period_year, period_month)",

            """
            CREATE TABLE IF NOT EXISTS payroll_runs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                period_id INTEGER NOT NULL REFERENCES payroll_periods(id),
                run_number INTEGER DEFAULT 1,
                run_type TEXT DEFAULT 'regular',
                status TEXT DEFAULT 'draft',
                total_employees INTEGER DEFAULT 0,
                total_gross REAL DEFAULT 0,
                total_deductions REAL DEFAULT 0,
                total_net REAL DEFAULT 0,
                run_by INTEGER REFERENCES users(id),
                run_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                posted_by INTEGER REFERENCES users(id),
                posted_at TIMESTAMP,
                notes TEXT
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_payroll_runs_period ON payroll_runs(period_id)",

            """
            CREATE TABLE IF NOT EXISTS payroll_entries (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                payroll_run_id INTEGER NOT NULL REFERENCES payroll_runs(id),
                period_id INTEGER NOT NULL REFERENCES payroll_periods(id),
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                period_year INTEGER NOT NULL,
                period_month INTEGER NOT NULL,
                working_days INTEGER DEFAULT 30,
                actual_days INTEGER DEFAULT 30,
                basic_salary REAL DEFAULT 0,
                housing_allowance REAL DEFAULT 0,
                transport_allowance REAL DEFAULT 0,
                food_allowance REAL DEFAULT 0,
                phone_allowance REAL DEFAULT 0,
                other_allowances REAL DEFAULT 0,
                overtime_amount REAL DEFAULT 0,
                bonus_amount REAL DEFAULT 0,
                commission_amount REAL DEFAULT 0,
                gross_salary REAL DEFAULT 0,
                gosi_employee REAL DEFAULT 0,
                gosi_employer REAL DEFAULT 0,
                gosi_base REAL DEFAULT 0,
                loan_deduction REAL DEFAULT 0,
                advance_deduction REAL DEFAULT 0,
                absence_deduction REAL DEFAULT 0,
                other_deductions REAL DEFAULT 0,
                total_deductions REAL DEFAULT 0,
                net_salary REAL DEFAULT 0,
                payment_method TEXT DEFAULT 'bank_transfer',
                bank_iban TEXT,
                status TEXT DEFAULT 'draft',
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_payroll_entries_run ON payroll_entries(payroll_run_id)",
            "CREATE INDEX IF NOT EXISTS idx_payroll_entries_employee ON payroll_entries(employee_id)",
            "CREATE INDEX IF NOT EXISTS idx_payroll_entries_period ON payroll_entries(period_id)",

            """
            CREATE TABLE IF NOT EXISTS payroll_adjustments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                period_id INTEGER NOT NULL REFERENCES payroll_periods(id),
                adjustment_type TEXT NOT NULL,
                description TEXT,
                amount REAL NOT NULL,
                is_addition INTEGER DEFAULT 1,
                is_recurring INTEGER DEFAULT 0,
                recurring_months INTEGER DEFAULT 0,
                start_period_id INTEGER REFERENCES payroll_periods(id),
                end_period_id INTEGER REFERENCES payroll_periods(id),
                approved_by INTEGER REFERENCES users(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # LOANS & ADVANCES
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS employee_loans (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                loan_number TEXT UNIQUE,
                loan_type TEXT DEFAULT 'personal',
                amount REAL NOT NULL,
                outstanding_amount REAL,
                installment_amount REAL,
                number_of_installments INTEGER,
                start_period_id INTEGER REFERENCES payroll_periods(id),
                disbursement_date DATE,
                disbursement_method TEXT DEFAULT 'bank_transfer',
                interest_rate REAL DEFAULT 0,
                reason TEXT,
                status TEXT DEFAULT 'pending',
                approved_by INTEGER REFERENCES users(id),
                approved_at TIMESTAMP,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_loans_employee ON employee_loans(employee_id)",

            """
            CREATE TABLE IF NOT EXISTS employee_advances (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                amount REAL NOT NULL,
                advance_date DATE DEFAULT CURRENT_DATE,
                reason TEXT,
                status TEXT DEFAULT 'pending',
                deduction_period_id INTEGER REFERENCES payroll_periods(id),
                approved_by INTEGER REFERENCES users(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS loan_repayments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                loan_id INTEGER NOT NULL REFERENCES employee_loans(id),
                period_id INTEGER NOT NULL REFERENCES payroll_periods(id),
                amount REAL NOT NULL,
                payment_date DATE,
                payroll_entry_id INTEGER REFERENCES payroll_entries(id),
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # LEAVE MANAGEMENT
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS leave_types (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                code TEXT NOT NULL,
                name TEXT NOT NULL,
                name_ar TEXT,
                days_per_year REAL DEFAULT 0,
                is_paid INTEGER DEFAULT 1,
                is_carry_forward INTEGER DEFAULT 0,
                max_carry_forward_days REAL DEFAULT 0,
                requires_approval INTEGER DEFAULT 1,
                min_advance_days INTEGER DEFAULT 0,
                max_consecutive_days INTEGER DEFAULT 0,
                applicable_gender TEXT DEFAULT 'all',
                is_active INTEGER DEFAULT 1,
                description TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS leave_requests (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                leave_type_id INTEGER NOT NULL REFERENCES leave_types(id),
                start_date DATE NOT NULL,
                end_date DATE NOT NULL,
                days_requested REAL,
                reason TEXT,
                status TEXT DEFAULT 'pending',
                applied_date TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                approved_by INTEGER REFERENCES users(id),
                approved_at TIMESTAMP,
                rejection_reason TEXT,
                replacement_employee_id INTEGER REFERENCES employees(id),
                return_date DATE,
                actual_return_date DATE,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_leave_requests_employee ON leave_requests(employee_id)",
            "CREATE INDEX IF NOT EXISTS idx_leave_requests_status ON leave_requests(status)",

            """
            CREATE TABLE IF NOT EXISTS leave_balances (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                leave_type_id INTEGER NOT NULL REFERENCES leave_types(id),
                year INTEGER NOT NULL,
                opening_balance REAL DEFAULT 0,
                accrued REAL DEFAULT 0,
                used REAL DEFAULT 0,
                carried_forward REAL DEFAULT 0,
                closing_balance REAL DEFAULT 0,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(employee_id, leave_type_id, year)
            )
            """,

            # =========================================================
            # ATTENDANCE & TIMESHEETS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS timesheets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                period_id INTEGER REFERENCES payroll_periods(id),
                week_start DATE,
                week_end DATE,
                total_hours REAL DEFAULT 0,
                overtime_hours REAL DEFAULT 0,
                status TEXT DEFAULT 'draft',
                submitted_at TIMESTAMP,
                approved_by INTEGER REFERENCES users(id),
                approved_at TIMESTAMP,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS attendance_records (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                employee_id INTEGER NOT NULL REFERENCES employees(id),
                attendance_date DATE NOT NULL,
                check_in TIME,
                check_out TIME,
                break_minutes INTEGER DEFAULT 0,
                total_hours REAL DEFAULT 0,
                overtime_hours REAL DEFAULT 0,
                status TEXT DEFAULT 'present',
                location TEXT,
                notes TEXT,
                source TEXT DEFAULT 'manual',
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(employee_id, attendance_date)
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_attendance_employee ON attendance_records(employee_id)",
            "CREATE INDEX IF NOT EXISTS idx_attendance_date ON attendance_records(attendance_date)",

            # =========================================================
            # ACCOUNTING
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS chart_of_accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                account_code TEXT NOT NULL,
                account_name TEXT NOT NULL,
                account_name_ar TEXT,
                account_type TEXT NOT NULL,
                account_subtype TEXT,
                parent_id INTEGER REFERENCES chart_of_accounts(id),
                level INTEGER DEFAULT 1,
                is_header INTEGER DEFAULT 0,
                is_active INTEGER DEFAULT 1,
                allow_posting INTEGER DEFAULT 1,
                normal_balance TEXT DEFAULT 'debit',
                description TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(company_id, account_code)
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_coa_company ON chart_of_accounts(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_coa_code ON chart_of_accounts(account_code)",
            "CREATE INDEX IF NOT EXISTS idx_coa_type ON chart_of_accounts(account_type)",

            """
            CREATE TABLE IF NOT EXISTS fiscal_periods (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                name TEXT NOT NULL,
                fiscal_year INTEGER NOT NULL,
                period_number INTEGER NOT NULL,
                start_date DATE NOT NULL,
                end_date DATE NOT NULL,
                status TEXT DEFAULT 'open',
                closed_by INTEGER REFERENCES users(id),
                closed_at TIMESTAMP,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(company_id, fiscal_year, period_number)
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS journal_entries (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                entry_number TEXT UNIQUE,
                entry_date DATE NOT NULL,
                description TEXT,
                reference TEXT,
                source_type TEXT,
                source_id INTEGER,
                status TEXT DEFAULT 'draft',
                total_debit REAL DEFAULT 0,
                total_credit REAL DEFAULT 0,
                fiscal_period_id INTEGER REFERENCES fiscal_periods(id),
                is_recurring INTEGER DEFAULT 0,
                recurring_template_id INTEGER,
                posted_by INTEGER REFERENCES users(id),
                posted_at TIMESTAMP,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_journal_entries_company ON journal_entries(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_journal_entries_date ON journal_entries(entry_date)",
            "CREATE INDEX IF NOT EXISTS idx_journal_entries_status ON journal_entries(status)",

            """
            CREATE TABLE IF NOT EXISTS journal_lines (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                journal_entry_id INTEGER NOT NULL REFERENCES journal_entries(id) ON DELETE CASCADE,
                account_id INTEGER NOT NULL REFERENCES chart_of_accounts(id),
                description TEXT,
                debit REAL DEFAULT 0,
                credit REAL DEFAULT 0,
                cost_center_id INTEGER REFERENCES cost_centers(id),
                department_id INTEGER REFERENCES departments(id),
                employee_id INTEGER REFERENCES employees(id),
                reference TEXT,
                sort_order INTEGER DEFAULT 0
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_journal_lines_entry ON journal_lines(journal_entry_id)",
            "CREATE INDEX IF NOT EXISTS idx_journal_lines_account ON journal_lines(account_id)",

            # =========================================================
            # BANKING
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS bank_accounts (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                account_name TEXT NOT NULL,
                bank_name TEXT NOT NULL,
                account_number TEXT NOT NULL,
                iban TEXT UNIQUE,
                swift_code TEXT,
                currency TEXT DEFAULT 'SAR',
                account_type TEXT DEFAULT 'current',
                gl_account_id INTEGER REFERENCES chart_of_accounts(id),
                opening_balance REAL DEFAULT 0,
                current_balance REAL DEFAULT 0,
                overdraft_limit REAL DEFAULT 0,
                branch_name TEXT,
                is_active INTEGER DEFAULT 1,
                is_wps_account INTEGER DEFAULT 0,
                wps_bank_code TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS bank_transactions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                bank_account_id INTEGER NOT NULL REFERENCES bank_accounts(id),
                transaction_date DATE NOT NULL,
                value_date DATE,
                description TEXT,
                reference TEXT,
                transaction_type TEXT,
                amount REAL NOT NULL,
                balance REAL,
                is_reconciled INTEGER DEFAULT 0,
                reconciliation_id INTEGER REFERENCES bank_reconciliation(id),
                journal_entry_id INTEGER REFERENCES journal_entries(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_bank_trans_account ON bank_transactions(bank_account_id)",
            "CREATE INDEX IF NOT EXISTS idx_bank_trans_date ON bank_transactions(transaction_date)",

            """
            CREATE TABLE IF NOT EXISTS bank_reconciliation (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                bank_account_id INTEGER NOT NULL REFERENCES bank_accounts(id),
                statement_date DATE NOT NULL,
                statement_balance REAL NOT NULL,
                book_balance REAL NOT NULL,
                outstanding_deposits REAL DEFAULT 0,
                outstanding_payments REAL DEFAULT 0,
                difference REAL DEFAULT 0,
                status TEXT DEFAULT 'in_progress',
                reconciled_by INTEGER REFERENCES users(id),
                reconciled_at TIMESTAMP,
                notes TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # INVOICING & PAYMENTS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS invoices (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                invoice_number TEXT UNIQUE,
                invoice_type TEXT DEFAULT 'standard',
                client_id INTEGER NOT NULL REFERENCES clients(id),
                contract_id INTEGER REFERENCES contracts(id),
                invoice_date DATE NOT NULL,
                due_date DATE,
                supply_date DATE,
                billing_period_start DATE,
                billing_period_end DATE,
                currency TEXT DEFAULT 'SAR',
                subtotal REAL DEFAULT 0,
                discount_amount REAL DEFAULT 0,
                vat_rate REAL DEFAULT 0.15,
                vat_amount REAL DEFAULT 0,
                total_amount REAL DEFAULT 0,
                paid_amount REAL DEFAULT 0,
                outstanding_amount REAL DEFAULT 0,
                status TEXT DEFAULT 'draft',
                payment_terms INTEGER DEFAULT 30,
                bank_account_id INTEGER REFERENCES bank_accounts(id),
                zatca_qr_code TEXT,
                zatca_uuid TEXT,
                zatca_hash TEXT,
                notes TEXT,
                terms_conditions TEXT,
                journal_entry_id INTEGER REFERENCES journal_entries(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_invoices_company ON invoices(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_invoices_client ON invoices(client_id)",
            "CREATE INDEX IF NOT EXISTS idx_invoices_status ON invoices(status)",
            "CREATE INDEX IF NOT EXISTS idx_invoices_date ON invoices(invoice_date)",

            """
            CREATE TABLE IF NOT EXISTS invoice_lines (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                invoice_id INTEGER NOT NULL REFERENCES invoices(id) ON DELETE CASCADE,
                description TEXT NOT NULL,
                quantity REAL DEFAULT 1,
                unit TEXT DEFAULT 'person_month',
                unit_price REAL DEFAULT 0,
                discount_percent REAL DEFAULT 0,
                discount_amount REAL DEFAULT 0,
                subtotal REAL DEFAULT 0,
                vat_rate REAL DEFAULT 0.15,
                vat_amount REAL DEFAULT 0,
                line_total REAL DEFAULT 0,
                account_id INTEGER REFERENCES chart_of_accounts(id),
                employee_id INTEGER REFERENCES employees(id),
                sort_order INTEGER DEFAULT 0
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_invoice_lines_invoice ON invoice_lines(invoice_id)",

            """
            CREATE TABLE IF NOT EXISTS payments (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                payment_number TEXT UNIQUE,
                client_id INTEGER REFERENCES clients(id),
                payment_date DATE NOT NULL,
                amount REAL NOT NULL,
                currency TEXT DEFAULT 'SAR',
                payment_method TEXT DEFAULT 'bank_transfer',
                reference TEXT,
                bank_account_id INTEGER REFERENCES bank_accounts(id),
                invoice_id INTEGER REFERENCES invoices(id),
                notes TEXT,
                status TEXT DEFAULT 'posted',
                journal_entry_id INTEGER REFERENCES journal_entries(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_payments_invoice ON payments(invoice_id)",
            "CREATE INDEX IF NOT EXISTS idx_payments_client ON payments(client_id)",

            """
            CREATE TABLE IF NOT EXISTS credit_notes (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                credit_note_number TEXT UNIQUE,
                client_id INTEGER NOT NULL REFERENCES clients(id),
                original_invoice_id INTEGER REFERENCES invoices(id),
                credit_note_date DATE NOT NULL,
                reason TEXT,
                subtotal REAL DEFAULT 0,
                vat_amount REAL DEFAULT 0,
                total_amount REAL DEFAULT 0,
                status TEXT DEFAULT 'draft',
                journal_entry_id INTEGER REFERENCES journal_entries(id),
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS credit_note_lines (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                credit_note_id INTEGER NOT NULL REFERENCES credit_notes(id) ON DELETE CASCADE,
                description TEXT NOT NULL,
                quantity REAL DEFAULT 1,
                unit_price REAL DEFAULT 0,
                subtotal REAL DEFAULT 0,
                vat_rate REAL DEFAULT 0.15,
                vat_amount REAL DEFAULT 0,
                line_total REAL DEFAULT 0,
                sort_order INTEGER DEFAULT 0
            )
            """,

            # =========================================================
            # ASSETS
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS assets (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                asset_number TEXT UNIQUE,
                asset_name TEXT NOT NULL,
                asset_name_ar TEXT,
                category TEXT,
                subcategory TEXT,
                description TEXT,
                serial_number TEXT,
                model TEXT,
                manufacturer TEXT,
                supplier TEXT,
                purchase_date DATE,
                purchase_price REAL DEFAULT 0,
                salvage_value REAL DEFAULT 0,
                useful_life_months INTEGER DEFAULT 60,
                depreciation_method TEXT DEFAULT 'straight_line',
                depreciation_rate REAL DEFAULT 0,
                accumulated_depreciation REAL DEFAULT 0,
                net_book_value REAL DEFAULT 0,
                department_id INTEGER REFERENCES departments(id),
                branch_id INTEGER REFERENCES branches(id),
                assigned_to INTEGER REFERENCES employees(id),
                location TEXT,
                condition TEXT DEFAULT 'good',
                is_active INTEGER DEFAULT 1,
                disposal_date DATE,
                disposal_reason TEXT,
                disposal_amount REAL DEFAULT 0,
                asset_account_id INTEGER REFERENCES chart_of_accounts(id),
                depreciation_account_id INTEGER REFERENCES chart_of_accounts(id),
                accumulated_dep_account_id INTEGER REFERENCES chart_of_accounts(id),
                warranty_expiry DATE,
                notes TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_assets_company ON assets(company_id)",
            "CREATE INDEX IF NOT EXISTS idx_assets_category ON assets(category)",

            """
            CREATE TABLE IF NOT EXISTS asset_depreciation (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                asset_id INTEGER NOT NULL REFERENCES assets(id),
                period TEXT NOT NULL,
                depreciation_date DATE NOT NULL,
                amount REAL NOT NULL,
                accumulated_amount REAL NOT NULL,
                net_book_value REAL NOT NULL,
                journal_entry_id INTEGER REFERENCES journal_entries(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(asset_id, period)
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS asset_maintenance (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                asset_id INTEGER NOT NULL REFERENCES assets(id),
                maintenance_type TEXT DEFAULT 'preventive',
                maintenance_date DATE NOT NULL,
                description TEXT,
                cost REAL DEFAULT 0,
                vendor TEXT,
                performed_by TEXT,
                next_maintenance_date DATE,
                documents_path TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            # =========================================================
            # COMPLIANCE (GOSI, WPS, ZATCA, VAT)
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS gosi_submissions (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                period_id INTEGER NOT NULL REFERENCES payroll_periods(id),
                submission_date DATE,
                total_employees INTEGER DEFAULT 0,
                total_saudi INTEGER DEFAULT 0,
                total_non_saudi INTEGER DEFAULT 0,
                total_employee_contribution REAL DEFAULT 0,
                total_employer_contribution REAL DEFAULT 0,
                total_amount REAL DEFAULT 0,
                status TEXT DEFAULT 'pending',
                reference_number TEXT,
                file_path TEXT,
                submitted_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS wps_files (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                payroll_run_id INTEGER NOT NULL REFERENCES payroll_runs(id),
                file_name TEXT,
                file_content TEXT,
                file_path TEXT,
                employer_id TEXT,
                pay_date DATE,
                total_records INTEGER DEFAULT 0,
                total_amount REAL DEFAULT 0,
                status TEXT DEFAULT 'generated',
                submission_date DATE,
                reference_number TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS zatca_invoices (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                invoice_id INTEGER NOT NULL REFERENCES invoices(id),
                invoice_uuid TEXT UNIQUE,
                invoice_hash TEXT,
                qr_code TEXT,
                xml_content TEXT,
                submission_id TEXT,
                status TEXT DEFAULT 'pending',
                submitted_at TIMESTAMP,
                clearance_status TEXT,
                reporting_status TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS vat_returns (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL REFERENCES companies(id),
                period_start DATE NOT NULL,
                period_end DATE NOT NULL,
                return_type TEXT DEFAULT 'quarterly',
                total_taxable_sales REAL DEFAULT 0,
                total_vat_on_sales REAL DEFAULT 0,
                total_taxable_purchases REAL DEFAULT 0,
                total_vat_on_purchases REAL DEFAULT 0,
                net_vat_due REAL DEFAULT 0,
                status TEXT DEFAULT 'draft',
                filing_date DATE,
                payment_date DATE,
                reference_number TEXT,
                notes TEXT,
                created_by INTEGER REFERENCES users(id),
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS vat_return_lines (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                vat_return_id INTEGER NOT NULL REFERENCES vat_returns(id),
                line_type TEXT NOT NULL,
                description TEXT,
                taxable_amount REAL DEFAULT 0,
                vat_amount REAL DEFAULT 0,
                adjustment_amount REAL DEFAULT 0,
                sort_order INTEGER DEFAULT 0
            )
            """,

            # =========================================================
            # SYSTEM TABLES
            # =========================================================
            """
            CREATE TABLE IF NOT EXISTS notifications (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER NOT NULL REFERENCES users(id),
                title TEXT NOT NULL,
                message TEXT,
                notification_type TEXT DEFAULT 'info',
                link TEXT,
                is_read INTEGER DEFAULT 0,
                read_at TIMESTAMP,
                expires_at TIMESTAMP,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_notifications_user ON notifications(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_notifications_read ON notifications(is_read)",

            """
            CREATE TABLE IF NOT EXISTS audit_logs (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                user_id INTEGER REFERENCES users(id),
                username TEXT,
                action TEXT NOT NULL,
                table_name TEXT,
                record_id INTEGER,
                old_values TEXT,
                new_values TEXT,
                ip_address TEXT,
                user_agent TEXT,
                created_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
            )
            """,
            "CREATE INDEX IF NOT EXISTS idx_audit_logs_user ON audit_logs(user_id)",
            "CREATE INDEX IF NOT EXISTS idx_audit_logs_table ON audit_logs(table_name)",
            "CREATE INDEX IF NOT EXISTS idx_audit_logs_date ON audit_logs(created_at)",

            """
            CREATE TABLE IF NOT EXISTS sequences (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER NOT NULL,
                sequence_name TEXT NOT NULL,
                prefix TEXT,
                suffix TEXT,
                current_value INTEGER DEFAULT 0,
                step INTEGER DEFAULT 1,
                padding INTEGER DEFAULT 5,
                UNIQUE(company_id, sequence_name)
            )
            """,

            """
            CREATE TABLE IF NOT EXISTS settings (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                company_id INTEGER REFERENCES companies(id),
                setting_key TEXT NOT NULL,
                setting_value TEXT,
                setting_type TEXT DEFAULT 'string',
                description TEXT,
                is_sensitive INTEGER DEFAULT 0,
                updated_by INTEGER REFERENCES users(id),
                updated_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP,
                UNIQUE(company_id, setting_key)
            )
            """,

            # Triggers for updated_at
            """
            CREATE TRIGGER IF NOT EXISTS update_companies_timestamp
            AFTER UPDATE ON companies
            BEGIN
                UPDATE companies SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
            END
            """,

            """
            CREATE TRIGGER IF NOT EXISTS update_employees_timestamp
            AFTER UPDATE ON employees
            BEGIN
                UPDATE employees SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
            END
            """,

            """
            CREATE TRIGGER IF NOT EXISTS update_invoices_timestamp
            AFTER UPDATE ON invoices
            BEGIN
                UPDATE invoices SET updated_at = CURRENT_TIMESTAMP WHERE id = NEW.id;
            END
            """,
        ]

        for sql in tables_sql:
            try:
                self.conn.execute(sql)
            except sqlite3.Error as e:
                logger.error(f"Error creating table/index: {e}\nSQL: {sql[:100]}")
                raise

        self.conn.commit()
        logger.info("Database tables created successfully")

        # Insert schema version
        current_version = self.get_schema_version()
        if current_version < self._version:
            self.execute(
                "INSERT INTO schema_version (version, description) VALUES (?, ?)",
                (self._version, "Initial schema")
            )

    def get_next_sequence(self, company_id: int, sequence_name: str) -> str:
        """Get the next value in a sequence."""
        with self._lock:
            seq = self.fetchone(
                "SELECT * FROM sequences WHERE company_id = ? AND sequence_name = ?",
                (company_id, sequence_name)
            )
            if not seq:
                # Create sequence
                defaults = {
                    'employee': ('EMP', '', 1, 1, 5),
                    'contract': ('CNT', '', 1, 1, 5),
                    'invoice': ('INV', '', 1, 1, 6),
                    'payment': ('PAY', '', 1, 1, 6),
                    'journal': ('JE', '', 1, 1, 6),
                    'loan': ('LN', '', 1, 1, 5),
                    'asset': ('AST', '', 1, 1, 5),
                    'client': ('CLI', '', 1, 1, 5),
                    'credit_note': ('CN', '', 1, 1, 6),
                    'payroll_run': ('PR', '', 1, 1, 6),
                }
                prefix, suffix, current, step, padding = defaults.get(
                    sequence_name, ('', '', 1, 1, 6)
                )
                self.execute(
                    """INSERT INTO sequences
                       (company_id, sequence_name, prefix, suffix, current_value, step, padding)
                       VALUES (?, ?, ?, ?, ?, ?, ?)""",
                    (company_id, sequence_name, prefix, suffix, current, step, padding)
                )
                seq = self.fetchone(
                    "SELECT * FROM sequences WHERE company_id = ? AND sequence_name = ?",
                    (company_id, sequence_name)
                )

            next_val = seq['current_value'] + seq['step']
            self.execute(
                "UPDATE sequences SET current_value = ? WHERE id = ?",
                (next_val, seq['id'])
            )

            number = str(next_val).zfill(seq['padding'])
            year = datetime.date.today().year
            return f"{seq['prefix']}{year}{number}{seq['suffix']}"

    def backup(self, backup_path: str = None) -> str:
        """Create a database backup."""
        if not backup_path:
            timestamp = datetime.datetime.now().strftime('%Y%m%d_%H%M%S')
            backup_dir = Path(self.db_path).parent / "backups"
            backup_dir.mkdir(exist_ok=True)
            backup_path = str(backup_dir / f"erp_backup_{timestamp}.db")

        import shutil
        shutil.copy2(self.db_path, backup_path)
        logger.info(f"Database backed up to: {backup_path}")
        return backup_path

    def vacuum(self):
        """Run VACUUM to optimize the database."""
        self.conn.execute("PRAGMA incremental_vacuum(100)")
        logger.info("Database vacuumed")


# =============================================================================
# SECTION 4: ORM-STYLE MODEL CLASSES
# =============================================================================

class BaseModel:
    """
    Base model class providing common functionality for all ERP models.
    Supports serialization, deserialization, and basic validation.
    """
    _table = ""
    _fields: List[str] = []

    def __init__(self, **kwargs):
        for key, value in kwargs.items():
            setattr(self, key, value)

    def to_dict(self) -> dict:
        """Convert model to dictionary."""
        result = {}
        for key, value in self.__dict__.items():
            if not key.startswith('_'):
                if isinstance(value, (datetime.date, datetime.datetime)):
                    result[key] = value.isoformat()
                elif isinstance(value, Decimal):
                    result[key] = float(value)
                else:
                    result[key] = value
        return result

    @classmethod
    def from_dict(cls, data: dict):
        """Create model from dictionary."""
        instance = cls()
        for key, value in data.items():
            setattr(instance, key, value)
        return instance

    def validate(self) -> List[str]:
        """Validate model and return list of errors."""
        return []

    def is_valid(self) -> bool:
        """Check if model is valid."""
        return len(self.validate()) == 0

    def __repr__(self):
        return f"{self.__class__.__name__}({self.to_dict()})"


class Company(BaseModel):
    """Company model."""
    _table = "companies"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.name: str = ""
        self.name_ar: str = ""
        self.cr_number: str = ""
        self.vat_number: str = ""
        self.address: str = ""
        self.city: str = ""
        self.country: str = "Saudi Arabia"
        self.phone: str = ""
        self.email: str = ""
        self.currency: str = "SAR"
        self.default_vat_rate: float = 0.15
        self.is_active: int = 1
        super().__init__(**kwargs)

    def validate(self) -> List[str]:
        errors = []
        if not self.name:
            errors.append("Company name is required")
        if not self.cr_number:
            errors.append("CR number is required")
        return errors


class Branch(BaseModel):
    """Branch model."""
    _table = "branches"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.name: str = ""
        self.name_ar: str = ""
        self.code: str = ""
        self.manager_name: str = ""
        self.address: str = ""
        self.city: str = ""
        self.phone: str = ""
        self.is_active: int = 1
        self.is_head_office: int = 0
        super().__init__(**kwargs)


class Department(BaseModel):
    """Department model."""
    _table = "departments"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.branch_id: Optional[int] = None
        self.parent_id: Optional[int] = None
        self.name: str = ""
        self.name_ar: str = ""
        self.code: str = ""
        self.manager_id: Optional[int] = None
        self.is_active: int = 1
        super().__init__(**kwargs)


class CostCenter(BaseModel):
    """Cost Center model."""
    _table = "cost_centers"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.code: str = ""
        self.name: str = ""
        self.budget: float = 0.0
        self.is_active: int = 1
        super().__init__(**kwargs)


class User(BaseModel):
    """User model."""
    _table = "users"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.username: str = ""
        self.password_hash: str = ""
        self.email: str = ""
        self.full_name: str = ""
        self.company_id: Optional[int] = None
        self.is_active: int = 1
        self.is_admin: int = 0
        self.language: str = "en"
        super().__init__(**kwargs)

    def validate(self) -> List[str]:
        errors = []
        if not self.username:
            errors.append("Username is required")
        if len(self.username) < 3:
            errors.append("Username must be at least 3 characters")
        return errors


class Role(BaseModel):
    """Role model."""
    _table = "roles"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.name: str = ""
        self.display_name: str = ""
        self.description: str = ""
        self.is_system: int = 0
        self.is_active: int = 1
        super().__init__(**kwargs)


class Client(BaseModel):
    """Client model."""
    _table = "clients"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.client_number: str = ""
        self.name: str = ""
        self.name_ar: str = ""
        self.cr_number: str = ""
        self.vat_number: str = ""
        self.industry: str = ""
        self.client_type: str = "corporate"
        self.address: str = ""
        self.city: str = ""
        self.country: str = "Saudi Arabia"
        self.phone: str = ""
        self.email: str = ""
        self.payment_terms: int = 30
        self.credit_limit: float = 0.0
        self.status: str = "active"
        self.notes: str = ""
        super().__init__(**kwargs)

    def validate(self) -> List[str]:
        errors = []
        if not self.name:
            errors.append("Client name is required")
        return errors


class Employee(BaseModel):
    """
    Employee model with all 50+ fields per Saudi labor requirements.
    """
    _table = "employees"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.emp_number: str = ""
        self.first_name: str = ""
        self.last_name: str = ""
        self.middle_name: str = ""
        self.arabic_name: str = ""
        self.nationality: str = ""
        self.id_type: str = "iqama"
        self.id_number: str = ""
        self.iqama_number: str = ""
        self.iqama_expiry: Optional[str] = None
        self.iqama_issue_place: str = ""
        self.passport_number: str = ""
        self.passport_expiry: Optional[str] = None
        self.passport_issue_country: str = ""
        self.visa_number: str = ""
        self.visa_type: str = ""
        self.visa_expiry: Optional[str] = None
        self.border_number: str = ""
        self.date_of_birth: Optional[str] = None
        self.gender: str = "male"
        self.marital_status: str = "single"
        self.religion: str = ""
        self.education: str = ""
        self.mobile: str = ""
        self.email: str = ""
        self.emergency_contact: str = ""
        self.emergency_phone: str = ""
        self.current_address: str = ""
        self.hire_date: Optional[str] = None
        self.termination_date: Optional[str] = None
        self.termination_reason: str = ""
        self.job_title: str = ""
        self.job_title_ar: str = ""
        self.department_id: Optional[int] = None
        self.branch_id: Optional[int] = None
        self.cost_center_id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.direct_manager_id: Optional[int] = None
        self.employment_type: str = "full_time"
        self.contract_type: str = "indefinite"
        self.salary_type: str = "monthly"
        self.basic_salary: float = 0.0
        self.housing_allowance: float = 0.0
        self.transport_allowance: float = 0.0
        self.food_allowance: float = 0.0
        self.phone_allowance: float = 0.0
        self.other_allowances: float = 0.0
        self.total_salary: float = 0.0
        self.bank_name: str = ""
        self.bank_account: str = ""
        self.bank_iban: str = ""
        self.payment_method: str = "bank_transfer"
        self.gosi_number: str = ""
        self.gosi_eligible: int = 1
        self.tax_number: str = ""
        self.is_saudi: int = 0
        self.is_active: int = 1
        self.is_on_leave: int = 0
        self.notes: str = ""
        self.photo_path: str = ""
        super().__init__(**kwargs)

    def validate(self) -> List[str]:
        errors = []
        if not self.first_name:
            errors.append("First name is required")
        if not self.nationality:
            errors.append("Nationality is required")
        if not self.hire_date:
            errors.append("Hire date is required")
        if self.basic_salary < 0:
            errors.append("Basic salary cannot be negative")
        return errors

    def get_full_name(self) -> str:
        """Get employee full name."""
        parts = [self.first_name]
        if self.middle_name:
            parts.append(self.middle_name)
        if self.last_name:
            parts.append(self.last_name)
        return " ".join(parts)

    def calculate_total_salary(self) -> float:
        """Calculate total monthly salary."""
        return (
            self.basic_salary + self.housing_allowance +
            self.transport_allowance + self.food_allowance +
            self.phone_allowance + self.other_allowances
        )

    def get_years_of_service(self, as_of_date: str = None) -> float:
        """Calculate years of service."""
        if not self.hire_date:
            return 0.0
        hire = datetime.date.fromisoformat(self.hire_date)
        if as_of_date:
            end = datetime.date.fromisoformat(as_of_date)
        elif self.termination_date:
            end = datetime.date.fromisoformat(self.termination_date)
        else:
            end = datetime.date.today()
        delta = end - hire
        return delta.days / 365.25


class Contract(BaseModel):
    """Contract model."""
    _table = "contracts"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.client_id: Optional[int] = None
        self.contract_number: str = ""
        self.title: str = ""
        self.description: str = ""
        self.contract_type: str = "manpower_supply"
        self.status: str = "draft"
        self.start_date: Optional[str] = None
        self.end_date: Optional[str] = None
        self.payment_terms: int = 30
        self.currency: str = "SAR"
        self.vat_applicable: int = 1
        self.total_value: float = 0.0
        self.notes: str = ""
        super().__init__(**kwargs)


class ContractLine(BaseModel):
    """Contract line model."""
    _table = "contract_lines"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.contract_id: Optional[int] = None
        self.description: str = ""
        self.quantity: float = 1.0
        self.unit: str = "person"
        self.unit_price: float = 0.0
        self.discount_percent: float = 0.0
        self.total_price: float = 0.0
        self.vat_rate: float = 0.15
        self.vat_amount: float = 0.0
        self.line_total: float = 0.0
        super().__init__(**kwargs)

    def calculate(self):
        """Calculate line totals."""
        self.total_price = self.quantity * self.unit_price
        discount = self.total_price * (self.discount_percent / 100)
        net = self.total_price - discount
        self.vat_amount = net * self.vat_rate
        self.line_total = net + self.vat_amount


class PayrollPeriod(BaseModel):
    """Payroll period model."""
    _table = "payroll_periods"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.period_name: str = ""
        self.period_year: int = datetime.date.today().year
        self.period_month: int = datetime.date.today().month
        self.start_date: Optional[str] = None
        self.end_date: Optional[str] = None
        self.payment_date: Optional[str] = None
        self.status: str = "open"
        self.total_employees: int = 0
        self.total_gross: float = 0.0
        self.total_net: float = 0.0
        super().__init__(**kwargs)


class PayrollRun(BaseModel):
    """Payroll run model."""
    _table = "payroll_runs"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.period_id: Optional[int] = None
        self.run_number: int = 1
        self.run_type: str = "regular"
        self.status: str = "draft"
        self.total_employees: int = 0
        self.total_gross: float = 0.0
        self.total_net: float = 0.0
        super().__init__(**kwargs)


class PayrollEntry(BaseModel):
    """Payroll entry model."""
    _table = "payroll_entries"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.payroll_run_id: Optional[int] = None
        self.period_id: Optional[int] = None
        self.employee_id: Optional[int] = None
        self.period_year: int = 0
        self.period_month: int = 0
        self.working_days: int = 30
        self.actual_days: int = 30
        self.basic_salary: float = 0.0
        self.housing_allowance: float = 0.0
        self.transport_allowance: float = 0.0
        self.food_allowance: float = 0.0
        self.other_allowances: float = 0.0
        self.overtime_amount: float = 0.0
        self.bonus_amount: float = 0.0
        self.gross_salary: float = 0.0
        self.gosi_employee: float = 0.0
        self.gosi_employer: float = 0.0
        self.gosi_base: float = 0.0
        self.loan_deduction: float = 0.0
        self.advance_deduction: float = 0.0
        self.absence_deduction: float = 0.0
        self.other_deductions: float = 0.0
        self.total_deductions: float = 0.0
        self.net_salary: float = 0.0
        self.status: str = "draft"
        super().__init__(**kwargs)


class EmployeeLoan(BaseModel):
    """Employee loan model."""
    _table = "employee_loans"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.employee_id: Optional[int] = None
        self.loan_number: str = ""
        self.loan_type: str = "personal"
        self.amount: float = 0.0
        self.outstanding_amount: float = 0.0
        self.installment_amount: float = 0.0
        self.number_of_installments: int = 0
        self.reason: str = ""
        self.status: str = "pending"
        super().__init__(**kwargs)


class LeaveType(BaseModel):
    """Leave type model."""
    _table = "leave_types"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.code: str = ""
        self.name: str = ""
        self.name_ar: str = ""
        self.days_per_year: float = 0.0
        self.is_paid: int = 1
        self.is_carry_forward: int = 0
        self.max_carry_forward_days: float = 0.0
        self.requires_approval: int = 1
        self.applicable_gender: str = "all"
        self.is_active: int = 1
        super().__init__(**kwargs)


class LeaveRequest(BaseModel):
    """Leave request model."""
    _table = "leave_requests"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.employee_id: Optional[int] = None
        self.leave_type_id: Optional[int] = None
        self.start_date: Optional[str] = None
        self.end_date: Optional[str] = None
        self.days_requested: float = 0.0
        self.reason: str = ""
        self.status: str = "pending"
        super().__init__(**kwargs)

    def calculate_days(self) -> float:
        """Calculate number of leave days."""
        if self.start_date and self.end_date:
            start = datetime.date.fromisoformat(self.start_date)
            end = datetime.date.fromisoformat(self.end_date)
            return (end - start).days + 1
        return 0.0


class Timesheet(BaseModel):
    """Timesheet model."""
    _table = "timesheets"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.employee_id: Optional[int] = None
        self.period_id: Optional[int] = None
        self.week_start: Optional[str] = None
        self.week_end: Optional[str] = None
        self.total_hours: float = 0.0
        self.overtime_hours: float = 0.0
        self.status: str = "draft"
        super().__init__(**kwargs)


class ChartOfAccount(BaseModel):
    """Chart of Account model."""
    _table = "chart_of_accounts"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.account_code: str = ""
        self.account_name: str = ""
        self.account_name_ar: str = ""
        self.account_type: str = ""
        self.account_subtype: str = ""
        self.parent_id: Optional[int] = None
        self.level: int = 1
        self.is_header: int = 0
        self.is_active: int = 1
        self.allow_posting: int = 1
        self.normal_balance: str = "debit"
        super().__init__(**kwargs)


class JournalEntry(BaseModel):
    """Journal entry model."""
    _table = "journal_entries"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.entry_number: str = ""
        self.entry_date: Optional[str] = None
        self.description: str = ""
        self.reference: str = ""
        self.source_type: str = ""
        self.source_id: Optional[int] = None
        self.status: str = "draft"
        self.total_debit: float = 0.0
        self.total_credit: float = 0.0
        self.lines: List[dict] = []
        super().__init__(**kwargs)

    def is_balanced(self) -> bool:
        """Check if journal entry is balanced."""
        return abs(self.total_debit - self.total_credit) < 0.01


class Invoice(BaseModel):
    """Invoice model."""
    _table = "invoices"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.invoice_number: str = ""
        self.invoice_type: str = "standard"
        self.client_id: Optional[int] = None
        self.contract_id: Optional[int] = None
        self.invoice_date: Optional[str] = None
        self.due_date: Optional[str] = None
        self.currency: str = "SAR"
        self.subtotal: float = 0.0
        self.discount_amount: float = 0.0
        self.vat_rate: float = 0.15
        self.vat_amount: float = 0.0
        self.total_amount: float = 0.0
        self.paid_amount: float = 0.0
        self.outstanding_amount: float = 0.0
        self.status: str = "draft"
        self.payment_terms: int = 30
        self.zatca_qr_code: str = ""
        self.notes: str = ""
        self.lines: List[dict] = []
        super().__init__(**kwargs)

    def validate(self) -> List[str]:
        errors = []
        if not self.client_id:
            errors.append("Client is required")
        if not self.invoice_date:
            errors.append("Invoice date is required")
        if not self.lines:
            errors.append("Invoice must have at least one line")
        return errors

    def calculate_totals(self):
        """Recalculate invoice totals from lines."""
        self.subtotal = sum(
            line.get('subtotal', line.get('quantity', 1) * line.get('unit_price', 0))
            for line in self.lines
        )
        self.vat_amount = sum(line.get('vat_amount', 0) for line in self.lines)
        self.total_amount = self.subtotal + self.vat_amount - self.discount_amount
        self.outstanding_amount = self.total_amount - self.paid_amount


class Payment(BaseModel):
    """Payment model."""
    _table = "payments"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.payment_number: str = ""
        self.client_id: Optional[int] = None
        self.payment_date: Optional[str] = None
        self.amount: float = 0.0
        self.currency: str = "SAR"
        self.payment_method: str = "bank_transfer"
        self.reference: str = ""
        self.invoice_id: Optional[int] = None
        self.status: str = "posted"
        super().__init__(**kwargs)


class Asset(BaseModel):
    """Asset model."""
    _table = "assets"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.company_id: Optional[int] = None
        self.asset_number: str = ""
        self.asset_name: str = ""
        self.category: str = ""
        self.purchase_date: Optional[str] = None
        self.purchase_price: float = 0.0
        self.salvage_value: float = 0.0
        self.useful_life_months: int = 60
        self.depreciation_method: str = "straight_line"
        self.accumulated_depreciation: float = 0.0
        self.net_book_value: float = 0.0
        self.is_active: int = 1
        super().__init__(**kwargs)

    def calculate_monthly_depreciation(self) -> float:
        """Calculate monthly depreciation amount."""
        depreciable_amount = self.purchase_price - self.salvage_value
        if self.useful_life_months <= 0:
            return 0.0
        if self.depreciation_method == "straight_line":
            return depreciable_amount / self.useful_life_months
        elif self.depreciation_method == "declining_balance":
            rate = self.depreciation_method / self.useful_life_months
            return self.net_book_value * rate / 12
        return depreciable_amount / self.useful_life_months


class AuditLog(BaseModel):
    """Audit log model."""
    _table = "audit_logs"

    def __init__(self, **kwargs):
        self.id: Optional[int] = None
        self.user_id: Optional[int] = None
        self.username: str = ""
        self.action: str = ""
        self.table_name: str = ""
        self.record_id: Optional[int] = None
        self.old_values: str = ""
        self.new_values: str = ""
        self.created_at: Optional[str] = None
        super().__init__(**kwargs)


# =============================================================================
# SECTION 5: REPOSITORY LAYER
# =============================================================================

class BaseRepository:
    """
    Base repository providing common CRUD operations.
    All specific repositories inherit from this class.
    """

    table: str = ""
    model_class = BaseModel

    def __init__(self, db: DatabaseManager):
        self.db = db
        self._logger = logging.getLogger(f"repo.{self.__class__.__name__}")

    def create(self, data: dict) -> int:
        """Create a new record and return its ID."""
        # Remove None values for cleaner inserts
        clean_data = {k: v for k, v in data.items() if v is not None and k != 'id'}
        try:
            row_id = self.db.insert(self.table, clean_data)
            self._logger.debug(f"Created {self.table} record with ID: {row_id}")
            return row_id
        except Exception as e:
            self._logger.error(f"Error creating {self.table}: {e}")
            raise

    def get_by_id(self, record_id: int) -> Optional[dict]:
        """Get a record by ID."""
        return self.db.fetchone(
            f"SELECT * FROM {self.table} WHERE id = ?",
            (record_id,)
        )

    def update(self, record_id: int, data: dict) -> bool:
        """Update a record by ID."""
        clean_data = {k: v for k, v in data.items() if k != 'id'}
        if not clean_data:
            return False
        rows = self.db.update(self.table, clean_data, "id = ?", (record_id,))
        return rows > 0

    def delete(self, record_id: int) -> bool:
        """Delete a record by ID."""
        rows = self.db.delete(self.table, "id = ?", (record_id,))
        return rows > 0

    def list_all(self, filters: dict = None, page: int = 1,
                 per_page: int = DEFAULT_PAGE_SIZE,
                 order_by: str = "id DESC") -> List[dict]:
        """List all records with optional filtering and pagination."""
        where_clauses = []
        params = []

        if filters:
            for key, value in filters.items():
                if value is not None and value != "":
                    if isinstance(value, str) and '%' in value:
                        where_clauses.append(f"{key} LIKE ?")
                    else:
                        where_clauses.append(f"{key} = ?")
                    params.append(value)

        where_sql = ""
        if where_clauses:
            where_sql = "WHERE " + " AND ".join(where_clauses)

        offset = (page - 1) * per_page
        sql = f"""
            SELECT * FROM {self.table}
            {where_sql}
            ORDER BY {order_by}
            LIMIT ? OFFSET ?
        """
        params.extend([per_page, offset])
        return self.db.fetchall(sql, tuple(params))

    def count(self, filters: dict = None) -> int:
        """Count records with optional filtering."""
        where_clauses = []
        params = []

        if filters:
            for key, value in filters.items():
                if value is not None and value != "":
                    where_clauses.append(f"{key} = ?")
                    params.append(value)

        where_sql = ""
        if where_clauses:
            where_sql = "WHERE " + " AND ".join(where_clauses)

        result = self.db.fetchscalar(
            f"SELECT COUNT(*) FROM {self.table} {where_sql}",
            tuple(params)
        )
        return result or 0

    def search(self, query: str, fields: List[str]) -> List[dict]:
        """Search records across specified fields."""
        if not fields or not query:
            return []
        conditions = " OR ".join([f"{f} LIKE ?" for f in fields])
        params = tuple([f"%{query}%"] * len(fields))
        return self.db.fetchall(
            f"SELECT * FROM {self.table} WHERE {conditions} LIMIT 100",
            params
        )

    def exists(self, field: str, value: Any, exclude_id: int = None) -> bool:
        """Check if a value exists in a field."""
        sql = f"SELECT 1 FROM {self.table} WHERE {field} = ?"
        params = [value]
        if exclude_id:
            sql += " AND id != ?"
            params.append(exclude_id)
        return self.db.fetchone(sql, tuple(params)) is not None


class CompanyRepository(BaseRepository):
    """Repository for company operations."""
    table = "companies"

    def get_active(self) -> List[dict]:
        """Get all active companies."""
        return self.db.fetchall("SELECT * FROM companies WHERE is_active = 1")

    def get_default(self) -> Optional[dict]:
        """Get the first active company (default)."""
        return self.db.fetchone(
            "SELECT * FROM companies WHERE is_active = 1 ORDER BY id LIMIT 1"
        )


class ClientRepository(BaseRepository):
    """Repository for client operations."""
    table = "clients"

    def get_by_vat(self, vat: str) -> Optional[dict]:
        """Get client by VAT number."""
        return self.db.fetchone(
            "SELECT * FROM clients WHERE vat_number = ?", (vat,)
        )

    def get_by_cr(self, cr: str) -> Optional[dict]:
        """Get client by CR number."""
        return self.db.fetchone(
            "SELECT * FROM clients WHERE cr_number = ?", (cr,)
        )

    def get_active(self, company_id: int) -> List[dict]:
        """Get active clients for a company."""
        return self.db.fetchall(
            "SELECT * FROM clients WHERE company_id = ? AND status = 'active' ORDER BY name",
            (company_id,)
        )

    def get_statement(self, client_id: int) -> dict:
        """Get client account statement."""
        client = self.get_by_id(client_id)
        if not client:
            return {}

        invoices = self.db.fetchall(
            """SELECT i.*, 'invoice' as type FROM invoices i
               WHERE i.client_id = ? AND i.status IN ('posted','partial','paid')
               ORDER BY i.invoice_date""",
            (client_id,)
        )
        payments = self.db.fetchall(
            """SELECT p.*, 'payment' as type FROM payments p
               WHERE p.client_id = ? ORDER BY p.payment_date""",
            (client_id,)
        )

        total_invoiced = sum(inv['total_amount'] for inv in invoices)
        total_paid = sum(pay['amount'] for pay in payments)

        return {
            'client': client,
            'invoices': invoices,
            'payments': payments,
            'total_invoiced': total_invoiced,
            'total_paid': total_paid,
            'balance': total_invoiced - total_paid
        }

    def search_clients(self, query: str) -> List[dict]:
        """Search clients by name, CR, or VAT."""
        return self.search(query, ['name', 'name_ar', 'cr_number', 'vat_number', 'phone'])


class EmployeeRepository(BaseRepository):
    """Repository for employee operations."""
    table = "employees"

    def get_active(self, company_id: int = None) -> List[dict]:
        """Get all active employees."""
        if company_id:
            return self.db.fetchall(
                """SELECT e.*, d.name as department_name, b.name as branch_name
                   FROM employees e
                   LEFT JOIN departments d ON e.department_id = d.id
                   LEFT JOIN branches b ON e.branch_id = b.id
                   WHERE e.is_active = 1 AND e.company_id = ?
                   ORDER BY e.emp_number""",
                (company_id,)
            )
        return self.db.fetchall(
            """SELECT e.*, d.name as department_name, b.name as branch_name
               FROM employees e
               LEFT JOIN departments d ON e.department_id = d.id
               LEFT JOIN branches b ON e.branch_id = b.id
               WHERE e.is_active = 1 ORDER BY e.emp_number"""
        )

    def get_by_department(self, dept_id: int) -> List[dict]:
        """Get employees by department."""
        return self.db.fetchall(
            "SELECT * FROM employees WHERE department_id = ? AND is_active = 1",
            (dept_id,)
        )

    def search_employees(self, query: str) -> List[dict]:
        """Search employees by multiple fields."""
        return self.db.fetchall(
            """SELECT e.*, d.name as department_name FROM employees e
               LEFT JOIN departments d ON e.department_id = d.id
               WHERE e.first_name LIKE ? OR e.last_name LIKE ?
               OR e.arabic_name LIKE ? OR e.emp_number LIKE ?
               OR e.iqama_number LIKE ? OR e.passport_number LIKE ?
               OR e.mobile LIKE ? OR e.email LIKE ?
               LIMIT 50""",
            tuple([f"%{query}%"] * 8)
        )

    def get_expiring_documents(self, days: int = 30) -> List[dict]:
        """Get employees with expiring documents."""
        cutoff = (datetime.date.today() + datetime.timedelta(days=days)).isoformat()
        today = datetime.date.today().isoformat()

        return self.db.fetchall(
            """SELECT e.id, e.emp_number, e.first_name, e.last_name, e.arabic_name,
                      e.iqama_number, e.iqama_expiry,
                      e.passport_number, e.passport_expiry,
                      e.visa_number, e.visa_expiry
               FROM employees e
               WHERE e.is_active = 1 AND (
                   (e.iqama_expiry IS NOT NULL AND e.iqama_expiry BETWEEN ? AND ?)
                   OR (e.passport_expiry IS NOT NULL AND e.passport_expiry BETWEEN ? AND ?)
                   OR (e.visa_expiry IS NOT NULL AND e.visa_expiry BETWEEN ? AND ?)
               )
               ORDER BY e.iqama_expiry, e.passport_expiry, e.visa_expiry""",
            (today, cutoff, today, cutoff, today, cutoff)
        )

    def get_with_details(self, employee_id: int) -> Optional[dict]:
        """Get employee with all related details."""
        emp = self.db.fetchone(
            """SELECT e.*, d.name as department_name, b.name as branch_name,
                      cc.name as cost_center_name
               FROM employees e
               LEFT JOIN departments d ON e.department_id = d.id
               LEFT JOIN branches b ON e.branch_id = b.id
               LEFT JOIN cost_centers cc ON e.cost_center_id = cc.id
               WHERE e.id = ?""",
            (employee_id,)
        )
        if emp:
            emp['documents'] = self.db.fetchall(
                "SELECT * FROM employee_documents WHERE employee_id = ? ORDER BY expiry_date",
                (employee_id,)
            )
            emp['dependents'] = self.db.fetchall(
                "SELECT * FROM employee_dependents WHERE employee_id = ?",
                (employee_id,)
            )
            emp['history'] = self.db.fetchall(
                "SELECT * FROM employee_history WHERE employee_id = ? ORDER BY created_at DESC LIMIT 20",
                (employee_id,)
            )
        return emp

    def get_nationality_stats(self) -> List[dict]:
        """Get employee count by nationality."""
        return self.db.fetchall(
            """SELECT nationality, COUNT(*) as count
               FROM employees WHERE is_active = 1
               GROUP BY nationality ORDER BY count DESC"""
        )

    def get_department_stats(self) -> List[dict]:
        """Get employee count by department."""
        return self.db.fetchall(
            """SELECT d.name as department, COUNT(e.id) as count
               FROM employees e
               JOIN departments d ON e.department_id = d.id
               WHERE e.is_active = 1
               GROUP BY d.id, d.name ORDER BY count DESC"""
        )


class ContractRepository(BaseRepository):
    """Repository for contract operations."""
    table = "contracts"

    def get_active_contracts(self, company_id: int = None) -> List[dict]:
        """Get active contracts."""
        sql = """SELECT c.*, cl.name as client_name
                 FROM contracts c
                 JOIN clients cl ON c.client_id = cl.id
                 WHERE c.status = 'active'"""
        if company_id:
            sql += " AND c.company_id = ?"
            return self.db.fetchall(sql, (company_id,))
        return self.db.fetchall(sql)

    def get_with_lines(self, contract_id: int) -> Optional[dict]:
        """Get contract with all its lines."""
        contract = self.get_by_id(contract_id)
        if contract:
            contract['lines'] = self.db.fetchall(
                "SELECT * FROM contract_lines WHERE contract_id = ? ORDER BY sort_order",
                (contract_id,)
            )
            contract['assignments'] = self.db.fetchall(
                """SELECT ea.*, e.first_name, e.last_name, e.emp_number
                   FROM employee_assignments ea
                   JOIN employees e ON ea.employee_id = e.id
                   WHERE ea.contract_id = ? AND ea.is_active = 1""",
                (contract_id,)
            )
        return contract

    def get_expiring(self, days: int = 30) -> List[dict]:
        """Get contracts expiring soon."""
        cutoff = (datetime.date.today() + datetime.timedelta(days=days)).isoformat()
        today = datetime.date.today().isoformat()
        return self.db.fetchall(
            """SELECT c.*, cl.name as client_name
               FROM contracts c JOIN clients cl ON c.client_id = cl.id
               WHERE c.status = 'active'
               AND c.end_date BETWEEN ? AND ?
               ORDER BY c.end_date""",
            (today, cutoff)
        )


class PayrollRepository(BaseRepository):
    """Repository for payroll operations."""
    table = "payroll_periods"

    def get_period_entries(self, period_id: int) -> List[dict]:
        """Get all payroll entries for a period."""
        return self.db.fetchall(
            """SELECT pe.*, e.first_name, e.last_name, e.emp_number,
                      e.bank_iban, e.bank_name, e.is_saudi, e.nationality
               FROM payroll_entries pe
               JOIN employees e ON pe.employee_id = e.id
               WHERE pe.period_id = ?
               ORDER BY e.emp_number""",
            (period_id,)
        )

    def get_run_entries(self, run_id: int) -> List[dict]:
        """Get entries for a payroll run."""
        return self.db.fetchall(
            """SELECT pe.*, e.first_name, e.last_name, e.emp_number,
                      e.bank_iban, e.bank_name, e.is_saudi, e.nationality,
                      e.department_id, d.name as department_name
               FROM payroll_entries pe
               JOIN employees e ON pe.employee_id = e.id
               LEFT JOIN departments d ON e.department_id = d.id
               WHERE pe.payroll_run_id = ?
               ORDER BY e.emp_number""",
            (run_id,)
        )

    def get_employee_history(self, employee_id: int, months: int = 12) -> List[dict]:
        """Get payroll history for an employee."""
        return self.db.fetchall(
            """SELECT pe.*, pp.period_name, pp.period_year, pp.period_month
               FROM payroll_entries pe
               JOIN payroll_periods pp ON pe.period_id = pp.id
               WHERE pe.employee_id = ?
               ORDER BY pp.period_year DESC, pp.period_month DESC
               LIMIT ?""",
            (employee_id, months)
        )

    def get_active_loans(self, employee_id: int) -> List[dict]:
        """Get active loans for an employee."""
        return self.db.fetchall(
            """SELECT * FROM employee_loans
               WHERE employee_id = ? AND status = 'approved'
               AND outstanding_amount > 0""",
            (employee_id,)
        )


class InvoiceRepository(BaseRepository):
    """Repository for invoice operations."""
    table = "invoices"

    def get_outstanding(self, company_id: int = None) -> List[dict]:
        """Get outstanding invoices."""
        sql = """SELECT i.*, c.name as client_name
                 FROM invoices i JOIN clients c ON i.client_id = c.id
                 WHERE i.status IN ('posted', 'partial') AND i.outstanding_amount > 0"""
        if company_id:
            sql += " AND i.company_id = ?"
            sql += " ORDER BY i.due_date"
            return self.db.fetchall(sql, (company_id,))
        sql += " ORDER BY i.due_date"
        return self.db.fetchall(sql)

    def get_by_client(self, client_id: int) -> List[dict]:
        """Get invoices for a client."""
        return self.db.fetchall(
            """SELECT * FROM invoices WHERE client_id = ?
               ORDER BY invoice_date DESC""",
            (client_id,)
        )

    def get_with_lines(self, invoice_id: int) -> Optional[dict]:
        """Get invoice with all lines."""
        invoice = self.get_by_id(invoice_id)
        if invoice:
            invoice['lines'] = self.db.fetchall(
                "SELECT * FROM invoice_lines WHERE invoice_id = ? ORDER BY sort_order",
                (invoice_id,)
            )
            invoice['payments'] = self.db.fetchall(
                "SELECT * FROM payments WHERE invoice_id = ? ORDER BY payment_date",
                (invoice_id,)
            )
        return invoice

    def get_overdue(self, company_id: int) -> List[dict]:
        """Get overdue invoices."""
        today = datetime.date.today().isoformat()
        return self.db.fetchall(
            """SELECT i.*, c.name as client_name,
                      julianday('now') - julianday(i.due_date) as days_overdue
               FROM invoices i JOIN clients c ON i.client_id = c.id
               WHERE i.company_id = ? AND i.status IN ('posted','partial')
               AND i.due_date < ? AND i.outstanding_amount > 0
               ORDER BY i.due_date""",
            (company_id, today)
        )

    def get_ar_aging(self, company_id: int) -> dict:
        """Get Accounts Receivable aging report."""
        today = datetime.date.today().isoformat()
        rows = self.db.fetchall(
            """SELECT c.name as client_name,
                      SUM(CASE WHEN julianday(?) - julianday(i.due_date) <= 0 THEN i.outstanding_amount ELSE 0 END) as current_amount,
                      SUM(CASE WHEN julianday(?) - julianday(i.due_date) BETWEEN 1 AND 30 THEN i.outstanding_amount ELSE 0 END) as d1_30,
                      SUM(CASE WHEN julianday(?) - julianday(i.due_date) BETWEEN 31 AND 60 THEN i.outstanding_amount ELSE 0 END) as d31_60,
                      SUM(CASE WHEN julianday(?) - julianday(i.due_date) BETWEEN 61 AND 90 THEN i.outstanding_amount ELSE 0 END) as d61_90,
                      SUM(CASE WHEN julianday(?) - julianday(i.due_date) > 90 THEN i.outstanding_amount ELSE 0 END) as over_90,
                      SUM(i.outstanding_amount) as total
               FROM invoices i JOIN clients c ON i.client_id = c.id
               WHERE i.company_id = ? AND i.outstanding_amount > 0
               AND i.status IN ('posted','partial')
               GROUP BY c.id, c.name ORDER BY total DESC""",
            (today, today, today, today, today, company_id)
        )
        return {'rows': rows, 'as_of': today}


class AccountingRepository(BaseRepository):
    """Repository for accounting operations."""
    table = "journal_entries"

    def get_trial_balance(self, company_id: int, start_date: str, end_date: str) -> List[dict]:
        """Get trial balance data."""
        return self.db.fetchall(
            """SELECT a.account_code, a.account_name, a.account_type, a.normal_balance,
                      SUM(jl.debit) as total_debit,
                      SUM(jl.credit) as total_credit,
                      CASE WHEN a.normal_balance = 'debit'
                           THEN SUM(jl.debit) - SUM(jl.credit)
                           ELSE SUM(jl.credit) - SUM(jl.debit)
                      END as balance
               FROM journal_lines jl
               JOIN journal_entries je ON jl.journal_entry_id = je.id
               JOIN chart_of_accounts a ON jl.account_id = a.id
               WHERE je.company_id = ? AND je.status = 'posted'
               AND je.entry_date BETWEEN ? AND ?
               GROUP BY a.id, a.account_code, a.account_name, a.account_type, a.normal_balance
               HAVING (SUM(jl.debit) > 0 OR SUM(jl.credit) > 0)
               ORDER BY a.account_code""",
            (company_id, start_date, end_date)
        )

    def get_ledger(self, account_id: int, start_date: str = None, end_date: str = None) -> List[dict]:
        """Get general ledger for an account."""
        params = [account_id]
        date_filter = ""
        if start_date and end_date:
            date_filter = "AND je.entry_date BETWEEN ? AND ?"
            params.extend([start_date, end_date])

        return self.db.fetchall(
            f"""SELECT je.entry_date, je.entry_number, je.description,
                       jl.description as line_description, jl.debit, jl.credit
                FROM journal_lines jl
                JOIN journal_entries je ON jl.journal_entry_id = je.id
                WHERE jl.account_id = ? AND je.status = 'posted'
                {date_filter}
                ORDER BY je.entry_date, je.id""",
            tuple(params)
        )

    def get_account_balance(self, account_id: int, as_of_date: str = None) -> float:
        """Get account balance as of a date."""
        if not as_of_date:
            as_of_date = datetime.date.today().isoformat()

        row = self.db.fetchone(
            """SELECT a.normal_balance,
                      COALESCE(SUM(jl.debit), 0) as total_debit,
                      COALESCE(SUM(jl.credit), 0) as total_credit
               FROM chart_of_accounts a
               LEFT JOIN journal_lines jl ON jl.account_id = a.id
               LEFT JOIN journal_entries je ON jl.journal_entry_id = je.id
                   AND je.status = 'posted' AND je.entry_date <= ?
               WHERE a.id = ?
               GROUP BY a.id, a.normal_balance""",
            (as_of_date, account_id)
        )
        if not row:
            return 0.0
        if row['normal_balance'] == 'debit':
            return row['total_debit'] - row['total_credit']
        return row['total_credit'] - row['total_debit']


class LeaveRepository(BaseRepository):
    """Repository for leave management."""
    table = "leave_requests"

    def get_employee_balance(self, emp_id: int, leave_type_id: int, year: int = None) -> float:
        """Get employee leave balance."""
        if not year:
            year = datetime.date.today().year

        balance = self.db.fetchone(
            """SELECT * FROM leave_balances
               WHERE employee_id = ? AND leave_type_id = ? AND year = ?""",
            (emp_id, leave_type_id, year)
        )
        if balance:
            return balance.get('closing_balance', 0.0)
        return 0.0

    def get_employee_leaves(self, emp_id: int, year: int = None) -> List[dict]:
        """Get all leaves for an employee."""
        if not year:
            year = datetime.date.today().year
        return self.db.fetchall(
            """SELECT lr.*, lt.name as leave_type_name
               FROM leave_requests lr
               JOIN leave_types lt ON lr.leave_type_id = lt.id
               WHERE lr.employee_id = ?
               AND strftime('%Y', lr.start_date) = ?
               ORDER BY lr.start_date DESC""",
            (emp_id, str(year))
        )

    def get_pending_approvals(self, approver_id: int = None) -> List[dict]:
        """Get pending leave requests."""
        return self.db.fetchall(
            """SELECT lr.*, e.first_name, e.last_name, e.emp_number,
                      lt.name as leave_type_name
               FROM leave_requests lr
               JOIN employees e ON lr.employee_id = e.id
               JOIN leave_types lt ON lr.leave_type_id = lt.id
               WHERE lr.status = 'pending'
               ORDER BY lr.applied_date"""
        )


class AssetRepository(BaseRepository):
    """Repository for asset management."""
    table = "assets"

    def get_depreciable(self, company_id: int) -> List[dict]:
        """Get assets that can be depreciated."""
        return self.db.fetchall(
            """SELECT * FROM assets
               WHERE company_id = ? AND is_active = 1
               AND net_book_value > salvage_value
               AND disposal_date IS NULL""",
            (company_id,)
        )

    def get_depreciation_schedule(self, asset_id: int) -> List[dict]:
        """Get depreciation schedule for an asset."""
        return self.db.fetchall(
            "SELECT * FROM asset_depreciation WHERE asset_id = ? ORDER BY depreciation_date",
            (asset_id,)
        )

    def get_by_category(self, category: str, company_id: int) -> List[dict]:
        """Get assets by category."""
        return self.db.fetchall(
            "SELECT * FROM assets WHERE company_id = ? AND category = ? AND is_active = 1",
            (company_id, category)
        )


# =============================================================================
# SECTION 6: SERVICE LAYER
# =============================================================================

class BaseService:
    """Base service class providing database access and logging."""

    def __init__(self, db: DatabaseManager):
        self.db = db
        self._logger = logging.getLogger(f"service.{self.__class__.__name__}")


class AuthService(BaseService):
    """Authentication and authorization service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.security = SecurityManager(db)

    def login(self, username: str, password: str) -> Optional[dict]:
        """Authenticate user and return user dict or None."""
        user = self.db.fetchone(
            "SELECT * FROM users WHERE username = ? AND is_active = 1",
            (username,)
        )
        if not user:
            self._logger.warning(f"Login failed: user '{username}' not found")
            return None

        # Check if account is locked
        if user.get('locked_until'):
            locked_until = datetime.datetime.fromisoformat(user['locked_until'])
            if datetime.datetime.now() < locked_until:
                self._logger.warning(f"Login failed: account locked for '{username}'")
                return None

        if not self.security.verify_password(password, user['password_hash']):
            # Increment failed attempts
            attempts = (user.get('login_attempts') or 0) + 1
            update_data = {'login_attempts': attempts}
            if attempts >= 5:
                locked_until = (datetime.datetime.now() + datetime.timedelta(minutes=30)).isoformat()
                update_data['locked_until'] = locked_until
                self._logger.warning(f"Account locked: '{username}' after {attempts} attempts")
            self.db.update('users', update_data, "id = ?", (user['id'],))
            return None

        # Successful login - reset attempts
        self.db.update('users', {
            'login_attempts': 0,
            'locked_until': None,
            'last_login': datetime.datetime.now().isoformat()
        }, "id = ?", (user['id'],))

        # Get user roles and permissions
        user_dict = dict(user)
        user_dict['roles'] = self.get_user_roles(user['id'])
        user_dict['permissions'] = self.get_user_permissions(user['id'])
        user_dict.pop('password_hash', None)  # Don't return password hash

        self.security.audit_log(user['id'], 'LOGIN', 'users', user['id'], 'User logged in')
        self._logger.info(f"User '{username}' logged in successfully")
        return user_dict

    def logout(self, user_id: int):
        """Log out a user."""
        self.security.audit_log(user_id, 'LOGOUT', 'users', user_id, 'User logged out')

    def hash_password(self, password: str) -> str:
        """Hash a password."""
        return self.security.hash_password(password)

    def change_password(self, user_id: int, old_password: str, new_password: str) -> bool:
        """Change user password."""
        user = self.db.fetchone("SELECT * FROM users WHERE id = ?", (user_id,))
        if not user:
            return False
        if not self.security.verify_password(old_password, user['password_hash']):
            return False
        new_hash = self.security.hash_password(new_password)
        self.db.update('users', {
            'password_hash': new_hash,
            'must_change_password': 0
        }, "id = ?", (user_id,))
        return True

    def reset_password(self, user_id: int, new_password: str) -> bool:
        """Reset user password (admin action)."""
        new_hash = self.security.hash_password(new_password)
        rows = self.db.update('users', {
            'password_hash': new_hash,
            'must_change_password': 1,
            'login_attempts': 0,
            'locked_until': None
        }, "id = ?", (user_id,))
        return rows > 0

    def check_permission(self, user_id: int, permission: str) -> bool:
        """Check if user has a specific permission."""
        user = self.db.fetchone("SELECT * FROM users WHERE id = ?", (user_id,))
        if not user:
            return False
        if user.get('is_admin'):
            return True
        return self.security.check_permission(user_id, permission)

    def get_user_permissions(self, user_id: int) -> List[str]:
        """Get all permissions for a user."""
        perms = self.db.fetchall(
            """SELECT DISTINCT p.code FROM permissions p
               JOIN role_permissions rp ON p.id = rp.permission_id
               JOIN user_roles ur ON rp.role_id = ur.role_id
               WHERE ur.user_id = ?""",
            (user_id,)
        )
        return [p['code'] for p in perms]

    def get_user_roles(self, user_id: int) -> List[dict]:
        """Get roles assigned to a user."""
        return self.db.fetchall(
            """SELECT r.* FROM roles r
               JOIN user_roles ur ON r.id = ur.role_id
               WHERE ur.user_id = ?""",
            (user_id,)
        )

    def assign_role(self, user_id: int, role_id: int) -> bool:
        """Assign a role to a user."""
        try:
            self.db.execute(
                "INSERT OR IGNORE INTO user_roles (user_id, role_id) VALUES (?, ?)",
                (user_id, role_id)
            )
            return True
        except Exception:
            return False

    def create_user(self, data: dict) -> int:
        """Create a new user."""
        password = data.pop('password', 'admin123')
        data['password_hash'] = self.hash_password(password)
        user_id = self.db.insert('users', data)
        return user_id


class EmployeeService(BaseService):
    """Comprehensive employee management service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = EmployeeRepository(db)

    def create_employee(self, data: dict, created_by: int = None) -> int:
        """Create a new employee with auto-generated employee number."""
        company_id = data.get('company_id', 1)

        # Auto-generate employee number if not provided
        if not data.get('emp_number'):
            data['emp_number'] = self.db.get_next_sequence(company_id, 'employee')

        # Calculate total salary
        data['total_salary'] = (
            data.get('basic_salary', 0) +
            data.get('housing_allowance', 0) +
            data.get('transport_allowance', 0) +
            data.get('food_allowance', 0) +
            data.get('phone_allowance', 0) +
            data.get('other_allowances', 0)
        )

        # Set probation end date if not provided (3 months)
        if data.get('hire_date') and not data.get('probation_end_date'):
            hire = datetime.date.fromisoformat(data['hire_date'])
            probation_end = hire + datetime.timedelta(days=90)
            data['probation_end_date'] = probation_end.isoformat()

        if created_by:
            data['created_by'] = created_by

        emp_id = self.db.insert('employees', data)

        # Initialize leave balances
        self._initialize_leave_balances(emp_id, company_id, data.get('hire_date'))

        # Log creation
        self._logger.info(f"Employee created: {data.get('emp_number')} (ID: {emp_id})")
        return emp_id

    def update_employee(self, emp_id: int, data: dict, updated_by: int = None) -> bool:
        """Update employee data and track changes."""
        old_emp = self.repo.get_by_id(emp_id)
        if not old_emp:
            return False

        # Recalculate total salary if salary fields changed
        salary_fields = ['basic_salary', 'housing_allowance', 'transport_allowance',
                        'food_allowance', 'phone_allowance', 'other_allowances']
        if any(f in data for f in salary_fields):
            data['total_salary'] = (
                data.get('basic_salary', old_emp.get('basic_salary', 0)) +
                data.get('housing_allowance', old_emp.get('housing_allowance', 0)) +
                data.get('transport_allowance', old_emp.get('transport_allowance', 0)) +
                data.get('food_allowance', old_emp.get('food_allowance', 0)) +
                data.get('phone_allowance', old_emp.get('phone_allowance', 0)) +
                data.get('other_allowances', old_emp.get('other_allowances', 0))
            )

        # Track important changes
        tracked_fields = ['basic_salary', 'job_title', 'department_id', 'branch_id']
        for field in tracked_fields:
            if field in data and data[field] != old_emp.get(field):
                self.db.insert('employee_history', {
                    'employee_id': emp_id,
                    'change_type': 'update',
                    'field_name': field,
                    'old_value': str(old_emp.get(field, '')),
                    'new_value': str(data[field]),
                    'effective_date': datetime.date.today().isoformat(),
                    'created_by': updated_by
                })

        rows = self.db.update('employees', data, "id = ?", (emp_id,))
        return rows > 0

    def terminate_employee(self, emp_id: int, termination_date: str,
                          reason: str, last_salary: bool = True) -> bool:
        """Terminate an employee."""
        emp = self.repo.get_by_id(emp_id)
        if not emp:
            return False

        rows = self.db.update('employees', {
            'is_active': 0,
            'termination_date': termination_date,
            'termination_reason': reason
        }, "id = ?", (emp_id,))

        if rows > 0:
            # Log termination
            self.db.insert('employee_history', {
                'employee_id': emp_id,
                'change_type': 'termination',
                'field_name': 'status',
                'old_value': 'active',
                'new_value': 'terminated',
                'effective_date': termination_date,
                'reason': reason
            })
            self._logger.info(f"Employee {emp_id} terminated on {termination_date}")
            return True
        return False

    def get_employee_details(self, emp_id: int) -> Optional[dict]:
        """Get full employee details including all related data."""
        return self.repo.get_with_details(emp_id)

    def get_dashboard_stats(self, company_id: int = 1) -> dict:
        """Get employee statistics for dashboard."""
        stats = {
            'total_employees': self.db.fetchscalar(
                "SELECT COUNT(*) FROM employees WHERE company_id = ? AND is_active = 1",
                (company_id,)
            ) or 0,
            'saudi_employees': self.db.fetchscalar(
                "SELECT COUNT(*) FROM employees WHERE company_id = ? AND is_active = 1 AND is_saudi = 1",
                (company_id,)
            ) or 0,
            'non_saudi_employees': self.db.fetchscalar(
                "SELECT COUNT(*) FROM employees WHERE company_id = ? AND is_active = 1 AND is_saudi = 0",
                (company_id,)
            ) or 0,
            'on_leave': self.db.fetchscalar(
                "SELECT COUNT(*) FROM employees WHERE company_id = ? AND is_on_leave = 1",
                (company_id,)
            ) or 0,
            'new_hires_this_month': self.db.fetchscalar(
                """SELECT COUNT(*) FROM employees
                   WHERE company_id = ? AND is_active = 1
                   AND strftime('%Y-%m', hire_date) = strftime('%Y-%m', 'now')""",
                (company_id,)
            ) or 0,
            'expiring_iqama_30': self.db.fetchscalar(
                """SELECT COUNT(*) FROM employees
                   WHERE company_id = ? AND is_active = 1
                   AND iqama_expiry BETWEEN date('now') AND date('now', '+30 days')""",
                (company_id,)
            ) or 0,
            'nationality_breakdown': self.db.fetchall(
                """SELECT nationality, COUNT(*) as count
                   FROM employees WHERE company_id = ? AND is_active = 1
                   GROUP BY nationality ORDER BY count DESC LIMIT 10""",
                (company_id,)
            ),
            'department_breakdown': self.db.fetchall(
                """SELECT d.name, COUNT(e.id) as count
                   FROM employees e JOIN departments d ON e.department_id = d.id
                   WHERE e.company_id = ? AND e.is_active = 1
                   GROUP BY d.id, d.name ORDER BY count DESC""",
                (company_id,)
            )
        }
        total = stats['total_employees'] or 1
        stats['saudization_rate'] = round((stats['saudi_employees'] / total) * 100, 1)
        return stats

    def _initialize_leave_balances(self, emp_id: int, company_id: int, hire_date: str = None):
        """Initialize leave balances for a new employee."""
        leave_types = self.db.fetchall(
            "SELECT * FROM leave_types WHERE company_id = ? AND is_active = 1",
            (company_id,)
        )
        year = datetime.date.today().year
        for lt in leave_types:
            # Calculate prorated balance if mid-year hire
            days = lt['days_per_year']
            if hire_date:
                try:
                    hire = datetime.date.fromisoformat(hire_date)
                    days_remaining = (datetime.date(year, 12, 31) - hire).days + 1
                    days = round(lt['days_per_year'] * days_remaining / 365, 1)
                except Exception:
                    pass

            self.db.execute(
                """INSERT OR IGNORE INTO leave_balances
                   (employee_id, leave_type_id, year, opening_balance, closing_balance)
                   VALUES (?, ?, ?, ?, ?)""",
                (emp_id, lt['id'], year, days, days)
            )


class ContractService(BaseService):
    """Contract management service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = ContractRepository(db)

    def create_contract(self, data: dict, lines: List[dict] = None) -> int:
        """Create a new contract with optional lines."""
        company_id = data.get('company_id', 1)
        if not data.get('contract_number'):
            data['contract_number'] = self.db.get_next_sequence(company_id, 'contract')

        contract_id = self.db.insert('contracts', data)

        if lines:
            for i, line in enumerate(lines):
                line['contract_id'] = contract_id
                line['sort_order'] = i
                # Calculate line totals
                qty = line.get('quantity', 1)
                price = line.get('unit_price', 0)
                disc = line.get('discount_percent', 0)
                total_price = qty * price
                discount_amt = total_price * (disc / 100)
                net = total_price - discount_amt
                vat_rate = line.get('vat_rate', 0.15)
                vat_amt = net * vat_rate
                line['total_price'] = total_price
                line['vat_amount'] = vat_amt
                line['line_total'] = net + vat_amt
                self.db.insert('contract_lines', line)

        # Update total value
        total = self.db.fetchscalar(
            "SELECT SUM(line_total) FROM contract_lines WHERE contract_id = ?",
            (contract_id,)
        ) or 0
        self.db.update('contracts', {'total_value': total}, "id = ?", (contract_id,))

        return contract_id

    def assign_employee(self, contract_id: int, emp_id: int, rate: float,
                       position: str = None, start_date: str = None) -> bool:
        """Assign an employee to a contract."""
        try:
            self.db.insert('employee_assignments', {
                'employee_id': emp_id,
                'contract_id': contract_id,
                'bill_rate': rate,
                'position': position,
                'assignment_date': start_date or datetime.date.today().isoformat(),
                'is_active': 1
            })
            return True
        except Exception as e:
            self._logger.error(f"Error assigning employee {emp_id} to contract {contract_id}: {e}")
            return False

    def get_contract_profitability(self, contract_id: int) -> dict:
        """Calculate contract profitability."""
        contract = self.repo.get_with_lines(contract_id)
        if not contract:
            return {}

        # Revenue from invoices
        revenue = self.db.fetchscalar(
            """SELECT COALESCE(SUM(subtotal), 0) FROM invoices
               WHERE contract_id = ? AND status IN ('posted','partial','paid')""",
            (contract_id,)
        ) or 0

        # Cost from employee assignments (salaries)
        cost = self.db.fetchscalar(
            """SELECT COALESCE(SUM(e.total_salary), 0)
               FROM employee_assignments ea
               JOIN employees e ON ea.employee_id = e.id
               WHERE ea.contract_id = ? AND ea.is_active = 1""",
            (contract_id,)
        ) or 0

        gross_profit = revenue - cost
        margin = (gross_profit / revenue * 100) if revenue > 0 else 0

        return {
            'contract': contract,
            'total_revenue': revenue,
            'total_cost': cost,
            'gross_profit': gross_profit,
            'margin_percent': round(margin, 2),
            'assigned_employees': len(contract.get('assignments', []))
        }


class LeaveService(BaseService):
    """Leave management service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = LeaveRepository(db)

    def request_leave(self, emp_id: int, leave_type_id: int,
                     start: str, end: str, reason: str = "") -> int:
        """Submit a leave request."""
        # Calculate days
        start_date = datetime.date.fromisoformat(start)
        end_date = datetime.date.fromisoformat(end)
        days = (end_date - start_date).days + 1

        if days <= 0:
            raise ValueError("End date must be after start date")

        # Check balance
        balance = self.repo.get_employee_balance(
            emp_id, leave_type_id, start_date.year
        )

        leave_type = self.db.fetchone("SELECT * FROM leave_types WHERE id = ?", (leave_type_id,))
        if leave_type and leave_type.get('is_paid') and balance < days:
            raise ValueError(f"Insufficient leave balance. Available: {balance} days, Requested: {days} days")

        request_id = self.db.insert('leave_requests', {
            'employee_id': emp_id,
            'leave_type_id': leave_type_id,
            'start_date': start,
            'end_date': end,
            'days_requested': days,
            'reason': reason,
            'status': 'pending',
            'applied_date': datetime.datetime.now().isoformat()
        })
        return request_id

    def approve_leave(self, request_id: int, approver_id: int) -> bool:
        """Approve a leave request."""
        request = self.db.fetchone("SELECT * FROM leave_requests WHERE id = ?", (request_id,))
        if not request or request['status'] != 'pending':
            return False

        self.db.update('leave_requests', {
            'status': 'approved',
            'approved_by': approver_id,
            'approved_at': datetime.datetime.now().isoformat()
        }, "id = ?", (request_id,))

        # Deduct from balance
        year = datetime.date.fromisoformat(request['start_date']).year
        self._deduct_balance(
            request['employee_id'],
            request['leave_type_id'],
            year,
            request['days_requested']
        )

        # Update employee leave status if current
        today = datetime.date.today().isoformat()
        if request['start_date'] <= today <= request['end_date']:
            self.db.update('employees', {'is_on_leave': 1},
                          "id = ?", (request['employee_id'],))

        return True

    def reject_leave(self, request_id: int, reason: str = "") -> bool:
        """Reject a leave request."""
        rows = self.db.update('leave_requests', {
            'status': 'rejected',
            'rejection_reason': reason
        }, "id = ?", (request_id,))
        return rows > 0

    def get_balance(self, emp_id: int, year: int = None) -> dict:
        """Get all leave balances for an employee."""
        if not year:
            year = datetime.date.today().year

        balances = self.db.fetchall(
            """SELECT lb.*, lt.name as leave_type_name, lt.code, lt.days_per_year
               FROM leave_balances lb
               JOIN leave_types lt ON lb.leave_type_id = lt.id
               WHERE lb.employee_id = ? AND lb.year = ?""",
            (emp_id, year)
        )
        return {b['code']: b for b in balances}

    def accrue_leave(self, emp_id: int, leave_type_id: int = None) -> bool:
        """Accrue monthly leave for an employee."""
        emp = self.db.fetchone("SELECT * FROM employees WHERE id = ?", (emp_id,))
        if not emp or not emp['is_active']:
            return False

        year = datetime.date.today().year
        company_id = emp['company_id']

        leave_types_query = "SELECT * FROM leave_types WHERE company_id = ? AND is_active = 1"
        params = [company_id]
        if leave_type_id:
            leave_types_query += " AND id = ?"
            params.append(leave_type_id)

        leave_types = self.db.fetchall(leave_types_query, tuple(params))

        for lt in leave_types:
            monthly_accrual = lt['days_per_year'] / 12.0

            # Get or create balance record
            balance = self.db.fetchone(
                "SELECT * FROM leave_balances WHERE employee_id = ? AND leave_type_id = ? AND year = ?",
                (emp_id, lt['id'], year)
            )

            if balance:
                new_accrued = balance['accrued'] + monthly_accrual
                new_closing = balance['opening_balance'] + new_accrued - balance['used']
                self.db.update('leave_balances', {
                    'accrued': new_accrued,
                    'closing_balance': new_closing,
                    'updated_at': datetime.datetime.now().isoformat()
                }, "id = ?", (balance['id'],))
            else:
                self.db.insert('leave_balances', {
                    'employee_id': emp_id,
                    'leave_type_id': lt['id'],
                    'year': year,
                    'opening_balance': 0,
                    'accrued': monthly_accrual,
                    'used': 0,
                    'closing_balance': monthly_accrual
                })
        return True

    def _deduct_balance(self, emp_id: int, leave_type_id: int, year: int, days: float):
        """Deduct days from leave balance."""
        balance = self.db.fetchone(
            "SELECT * FROM leave_balances WHERE employee_id = ? AND leave_type_id = ? AND year = ?",
            (emp_id, leave_type_id, year)
        )
        if balance:
            new_used = balance['used'] + days
            new_closing = balance['closing_balance'] - days
            self.db.update('leave_balances', {
                'used': new_used,
                'closing_balance': max(0, new_closing),
                'updated_at': datetime.datetime.now().isoformat()
            }, "id = ?", (balance['id'],))


class InvoiceService(BaseService):
    """Invoice and billing service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = InvoiceRepository(db)
        self.zatca = ZATCAEngine(db)
        self.accounting = AccountingService(db)

    def create_invoice(self, data: dict, lines: List[dict]) -> int:
        """Create a new invoice with line items."""
        company_id = data.get('company_id', 1)
        if not data.get('invoice_number'):
            data['invoice_number'] = self.db.get_next_sequence(company_id, 'invoice')

        # Set due date if not provided
        if not data.get('due_date') and data.get('invoice_date'):
            invoice_date = datetime.date.fromisoformat(data['invoice_date'])
            payment_terms = data.get('payment_terms', 30)
            data['due_date'] = (invoice_date + datetime.timedelta(days=payment_terms)).isoformat()

        # Calculate totals from lines
        subtotal = 0
        total_vat = 0
        for line in lines:
            qty = line.get('quantity', 1)
            price = line.get('unit_price', 0)
            disc_pct = line.get('discount_percent', 0)
            vat_rate = line.get('vat_rate', data.get('vat_rate', 0.15))

            line_subtotal = qty * price
            disc_amt = line_subtotal * (disc_pct / 100)
            net = line_subtotal - disc_amt
            vat_amt = net * vat_rate

            line['subtotal'] = round(net, 2)
            line['discount_amount'] = round(disc_amt, 2)
            line['vat_amount'] = round(vat_amt, 2)
            line['line_total'] = round(net + vat_amt, 2)

            subtotal += net
            total_vat += vat_amt

        data['subtotal'] = round(subtotal, 2)
        data['vat_amount'] = round(total_vat, 2)
        data['total_amount'] = round(subtotal + total_vat - data.get('discount_amount', 0), 2)
        data['outstanding_amount'] = data['total_amount']
        data['paid_amount'] = 0
        data['status'] = 'draft'

        invoice_id = self.db.insert('invoices', data)

        for i, line in enumerate(lines):
            line['invoice_id'] = invoice_id
            line['sort_order'] = i
            self.db.insert('invoice_lines', line)

        return invoice_id

    def post_invoice(self, invoice_id: int, posted_by: int = None) -> bool:
        """Post an invoice and create journal entry."""
        invoice = self.repo.get_with_lines(invoice_id)
        if not invoice or invoice['status'] != 'draft':
            return False

        company_id = invoice['company_id']

        # Generate ZATCA QR
        qr_code = self.zatca.generate_qr_code(invoice)

        # Get client AR account
        ar_account = self.db.fetchone(
            "SELECT * FROM chart_of_accounts WHERE company_id = ? AND account_code = '1200'",
            (company_id,)
        )
        revenue_account = self.db.fetchone(
            "SELECT * FROM chart_of_accounts WHERE company_id = ? AND account_code = '4100'",
            (company_id,)
        )
        vat_account = self.db.fetchone(
            "SELECT * FROM chart_of_accounts WHERE company_id = ? AND account_code = '2300'",
            (company_id,)
        )

        if ar_account and revenue_account:
            # Create journal entry
            je_data = {
                'company_id': company_id,
                'entry_number': self.db.get_next_sequence(company_id, 'journal'),
                'entry_date': invoice['invoice_date'],
                'description': f"Invoice {invoice['invoice_number']}",
                'source_type': 'invoice',
                'source_id': invoice_id
            }
            lines = [
                {'account_id': ar_account['id'], 'debit': invoice['total_amount'],
                 'credit': 0, 'description': f"AR - {invoice['invoice_number']}"},
                {'account_id': revenue_account['id'], 'debit': 0,
                 'credit': invoice['subtotal'], 'description': 'Service revenue'},
            ]
            if invoice['vat_amount'] > 0 and vat_account:
                lines.append({
                    'account_id': vat_account['id'], 'debit': 0,
                    'credit': invoice['vat_amount'], 'description': 'Output VAT'
                })

            je_id = self.accounting.create_journal_entry(je_data, lines)
            self.accounting.post_journal_entry(je_id)

            self.db.update('invoices', {
                'status': 'posted',
                'zatca_qr_code': qr_code,
                'zatca_uuid': str(uuid.uuid4()),
                'journal_entry_id': je_id
            }, "id = ?", (invoice_id,))
        else:
            self.db.update('invoices', {
                'status': 'posted',
                'zatca_qr_code': qr_code,
                'zatca_uuid': str(uuid.uuid4())
            }, "id = ?", (invoice_id,))

        return True

    def record_payment(self, invoice_id: int, amount: float,
                      payment_date: str, method: str = "bank_transfer",
                      reference: str = "") -> int:
        """Record a payment against an invoice."""
        invoice = self.repo.get_by_id(invoice_id)
        if not invoice:
            raise ValueError("Invoice not found")

        outstanding = invoice.get('outstanding_amount', 0)
        if amount > outstanding:
            raise ValueError(f"Payment amount ({amount}) exceeds outstanding ({outstanding})")

        company_id = invoice['company_id']
        payment_number = self.db.get_next_sequence(company_id, 'payment')

        payment_id = self.db.insert('payments', {
            'company_id': company_id,
            'payment_number': payment_number,
            'client_id': invoice['client_id'],
            'payment_date': payment_date,
            'amount': amount,
            'payment_method': method,
            'reference': reference,
            'invoice_id': invoice_id,
            'status': 'posted'
        })

        # Update invoice
        new_paid = invoice.get('paid_amount', 0) + amount
        new_outstanding = invoice['total_amount'] - new_paid
        new_status = 'paid' if new_outstanding <= 0.01 else 'partial'

        self.db.update('invoices', {
            'paid_amount': round(new_paid, 2),
            'outstanding_amount': max(0, round(new_outstanding, 2)),
            'status': new_status
        }, "id = ?", (invoice_id,))

        return payment_id

    def generate_zatca_qr(self, invoice_id: int) -> str:
        """Generate ZATCA QR code for an invoice."""
        invoice = self.repo.get_by_id(invoice_id)
        if not invoice:
            return ""
        return self.zatca.generate_qr_code(invoice)


class AccountingService(BaseService):
    """Accounting and financial management service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = AccountingRepository(db)

    def create_journal_entry(self, data: dict, lines: List[dict]) -> int:
        """Create a journal entry with lines."""
        company_id = data.get('company_id', 1)
        if not data.get('entry_number'):
            data['entry_number'] = self.db.get_next_sequence(company_id, 'journal')

        total_debit = sum(l.get('debit', 0) for l in lines)
        total_credit = sum(l.get('credit', 0) for l in lines)

        if abs(total_debit - total_credit) > 0.01:
            raise ValueError(
                f"Journal entry is not balanced: Debit {total_debit}, Credit {total_credit}"
            )

        data['total_debit'] = round(total_debit, 2)
        data['total_credit'] = round(total_credit, 2)
        data['status'] = 'draft'

        je_id = self.db.insert('journal_entries', data)

        for i, line in enumerate(lines):
            line['journal_entry_id'] = je_id
            line['sort_order'] = i
            self.db.insert('journal_lines', line)

        return je_id

    def post_journal_entry(self, entry_id: int, posted_by: int = None) -> bool:
        """Post a journal entry (mark as final)."""
        entry = self.db.fetchone("SELECT * FROM journal_entries WHERE id = ?", (entry_id,))
        if not entry or entry['status'] != 'draft':
            return False

        self.db.update('journal_entries', {
            'status': 'posted',
            'posted_by': posted_by,
            'posted_at': datetime.datetime.now().isoformat()
        }, "id = ?", (entry_id,))
        return True

    def get_trial_balance(self, company_id: int, start_date: str, end_date: str) -> List[dict]:
        """Get trial balance."""
        return self.repo.get_trial_balance(company_id, start_date, end_date)

    def get_profit_loss(self, company_id: int, start_date: str, end_date: str) -> dict:
        """Generate Profit & Loss statement."""
        rows = self.db.fetchall(
            """SELECT a.account_code, a.account_name, a.account_type, a.account_subtype,
                      a.normal_balance,
                      COALESCE(SUM(jl.debit), 0) as total_debit,
                      COALESCE(SUM(jl.credit), 0) as total_credit
               FROM chart_of_accounts a
               LEFT JOIN journal_lines jl ON jl.account_id = a.id
               LEFT JOIN journal_entries je ON jl.journal_entry_id = je.id
                   AND je.status = 'posted' AND je.company_id = ?
                   AND je.entry_date BETWEEN ? AND ?
               WHERE a.company_id = ? AND a.account_type IN ('revenue', 'expense')
               AND a.is_header = 0
               GROUP BY a.id, a.account_code, a.account_name, a.account_type, a.account_subtype, a.normal_balance
               ORDER BY a.account_code""",
            (company_id, start_date, end_date, company_id)
        )

        revenue = []
        expenses = []
        total_revenue = 0
        total_expenses = 0

        for row in rows:
            if row['normal_balance'] == 'credit':
                balance = row['total_credit'] - row['total_debit']
            else:
                balance = row['total_debit'] - row['total_credit']

            row['balance'] = round(balance, 2)

            if row['account_type'] == 'revenue':
                revenue.append(row)
                total_revenue += balance
            else:
                expenses.append(row)
                total_expenses += balance

        net_profit = total_revenue - total_expenses

        return {
            'period': f"{start_date} to {end_date}",
            'revenue': revenue,
            'expenses': expenses,
            'total_revenue': round(total_revenue, 2),
            'total_expenses': round(total_expenses, 2),
            'net_profit': round(net_profit, 2),
            'is_profit': net_profit >= 0
        }

    def get_balance_sheet(self, company_id: int, as_of_date: str) -> dict:
        """Generate Balance Sheet."""
        rows = self.db.fetchall(
            """SELECT a.account_code, a.account_name, a.account_type, a.account_subtype,
                      a.normal_balance,
                      COALESCE(SUM(jl.debit), 0) as total_debit,
                      COALESCE(SUM(jl.credit), 0) as total_credit
               FROM chart_of_accounts a
               LEFT JOIN journal_lines jl ON jl.account_id = a.id
               LEFT JOIN journal_entries je ON jl.journal_entry_id = je.id
                   AND je.status = 'posted' AND je.company_id = ?
                   AND je.entry_date <= ?
               WHERE a.company_id = ? AND a.account_type IN ('asset', 'liability', 'equity')
               AND a.is_header = 0
               GROUP BY a.id, a.account_code, a.account_name, a.account_type, a.account_subtype, a.normal_balance
               ORDER BY a.account_code""",
            (company_id, as_of_date, company_id)
        )

        assets = []
        liabilities = []
        equity = []
        total_assets = 0
        total_liabilities = 0
        total_equity = 0

        for row in rows:
            if row['normal_balance'] == 'debit':
                balance = row['total_debit'] - row['total_credit']
            else:
                balance = row['total_credit'] - row['total_debit']

            row['balance'] = round(balance, 2)

            if row['account_type'] == 'asset':
                assets.append(row)
                total_assets += balance
            elif row['account_type'] == 'liability':
                liabilities.append(row)
                total_liabilities += balance
            else:
                equity.append(row)
                total_equity += balance

        return {
            'as_of': as_of_date,
            'assets': assets,
            'liabilities': liabilities,
            'equity': equity,
            'total_assets': round(total_assets, 2),
            'total_liabilities': round(total_liabilities, 2),
            'total_equity': round(total_equity, 2),
            'is_balanced': abs(total_assets - (total_liabilities + total_equity)) < 1.0
        }

    def reconcile_bank(self, bank_account_id: int, statement_date: str,
                      statement_balance: float) -> dict:
        """Perform bank reconciliation."""
        bank_account = self.db.fetchone(
            "SELECT * FROM bank_accounts WHERE id = ?", (bank_account_id,)
        )
        if not bank_account:
            return {}

        # Get unreconciled transactions
        unreconciled = self.db.fetchall(
            """SELECT * FROM bank_transactions
               WHERE bank_account_id = ? AND is_reconciled = 0
               AND transaction_date <= ?
               ORDER BY transaction_date""",
            (bank_account_id, statement_date)
        )

        book_balance = self.db.fetchscalar(
            """SELECT COALESCE(SUM(CASE WHEN amount > 0 THEN amount ELSE 0 END) -
                               SUM(CASE WHEN amount < 0 THEN ABS(amount) ELSE 0 END), 0)
               FROM bank_transactions WHERE bank_account_id = ? AND transaction_date <= ?""",
            (bank_account_id, statement_date)
        ) or 0

        return {
            'bank_account': bank_account,
            'statement_date': statement_date,
            'statement_balance': statement_balance,
            'book_balance': book_balance,
            'difference': round(statement_balance - book_balance, 2),
            'unreconciled_transactions': unreconciled,
            'is_reconciled': abs(statement_balance - book_balance) < 0.01
        }


class AssetService(BaseService):
    """Fixed asset management service."""

    def __init__(self, db: DatabaseManager):
        super().__init__(db)
        self.repo = AssetRepository(db)

    def register_asset(self, data: dict) -> int:
        """Register a new asset."""
        company_id = data.get('company_id', 1)
        if not data.get('asset_number'):
            data['asset_number'] = self.db.get_next_sequence(company_id, 'asset')

        purchase_price = data.get('purchase_price', 0)
        data['net_book_value'] = purchase_price
        data['accumulated_depreciation'] = 0

        asset_id = self.db.insert('assets', data)
        return asset_id

    def calculate_depreciation(self, asset_id: int) -> float:
        """Calculate monthly depreciation for an asset."""
        asset = self.repo.get_by_id(asset_id)
        if not asset:
            return 0.0

        depreciable_amount = asset['purchase_price'] - asset.get('salvage_value', 0)
        useful_life = asset.get('useful_life_months', 60)

        if useful_life <= 0 or depreciable_amount <= 0:
            return 0.0

        method = asset.get('depreciation_method', 'straight_line')
        if method == 'straight_line':
            monthly_dep = depreciable_amount / useful_life
        elif method == 'declining_balance':
            rate = asset.get('depreciation_rate', 40) / 100
            monthly_dep = asset.get('net_book_value', 0) * rate / 12
        else:
            monthly_dep = depreciable_amount / useful_life

        # Don't depreciate below salvage value
        nbv = asset.get('net_book_value', 0)
        salvage = asset.get('salvage_value', 0)
        if nbv - monthly_dep < salvage:
            monthly_dep = max(0, nbv - salvage)

        return round(monthly_dep, 2)

    def run_depreciation_batch(self, company_id: int, period: str) -> dict:
        """Run depreciation for all assets in a period."""
        assets = self.repo.get_depreciable(company_id)
        results = {
            'period': period,
            'assets_processed': 0,
            'total_depreciation': 0,
            'errors': []
        }

        for asset in assets:
            try:
                amount = self.calculate_depreciation(asset['id'])
                if amount <= 0:
                    continue

                # Check if already depreciated for this period
                existing = self.db.fetchone(
                    "SELECT id FROM asset_depreciation WHERE asset_id = ? AND period = ?",
                    (asset['id'], period)
                )
                if existing:
                    continue

                new_accumulated = asset.get('accumulated_depreciation', 0) + amount
                new_nbv = asset['purchase_price'] - new_accumulated

                self.db.insert('asset_depreciation', {
                    'asset_id': asset['id'],
                    'period': period,
                    'depreciation_date': datetime.date.today().isoformat(),
                    'amount': amount,
                    'accumulated_amount': new_accumulated,
                    'net_book_value': max(0, new_nbv)
                })

                self.db.update('assets', {
                    'accumulated_depreciation': new_accumulated,
                    'net_book_value': max(0, new_nbv)
                }, "id = ?", (asset['id'],))

                results['assets_processed'] += 1
                results['total_depreciation'] += amount

            except Exception as e:
                results['errors'].append({'asset_id': asset['id'], 'error': str(e)})

        results['total_depreciation'] = round(results['total_depreciation'], 2)
        return results


class NotificationService(BaseService):
    """Notification management service."""

    def create_notification(self, user_id: int, title: str, message: str,
                           notification_type: str = 'info',
                           expires_in_days: int = 30) -> int:
        """Create a new notification."""
        expires_at = (datetime.datetime.now() + datetime.timedelta(days=expires_in_days)).isoformat()
        notification_id = self.db.insert('notifications', {
            'user_id': user_id,
            'title': title,
            'message': message,
            'notification_type': notification_type,
            'is_read': 0,
            'expires_at': expires_at
        })
        return notification_id

    def get_unread(self, user_id: int) -> List[dict]:
        """Get unread notifications for a user."""
        return self.db.fetchall(
            """SELECT * FROM notifications
               WHERE user_id = ? AND is_read = 0
               AND (expires_at IS NULL OR expires_at > datetime('now'))
               ORDER BY created_at DESC LIMIT 20""",
            (user_id,)
        )

    def mark_read(self, notification_id: int) -> bool:
        """Mark a notification as read."""
        rows = self.db.update('notifications', {
            'is_read': 1,
            'read_at': datetime.datetime.now().isoformat()
        }, "id = ?", (notification_id,))
        return rows > 0

    def mark_all_read(self, user_id: int) -> int:
        """Mark all notifications as read for a user."""
        cursor = self.db.execute(
            "UPDATE notifications SET is_read = 1, read_at = datetime('now') WHERE user_id = ? AND is_read = 0",
            (user_id,)
        )
        return cursor.rowcount

    def get_unread_count(self, user_id: int) -> int:
        """Get count of unread notifications."""
        return self.db.fetchscalar(
            "SELECT COUNT(*) FROM notifications WHERE user_id = ? AND is_read = 0",
            (user_id,)
        ) or 0


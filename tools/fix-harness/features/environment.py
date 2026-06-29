import os
import tempfile
import threading

import quickfix as fix

FIX_PORT = int(os.environ.get("FIX_PORT", "9878"))


class HarnessApp(fix.Application):
    def __init__(self):
        super().__init__()
        self.logon_event = threading.Event()
        self.session_id = None

    def onCreate(self, sessionID):
        pass

    def onLogon(self, sessionID):
        self.session_id = sessionID
        self.logon_event.set()

    def onLogout(self, sessionID):
        self.logon_event.clear()

    def toAdmin(self, message, sessionID):
        pass

    def fromAdmin(self, message, sessionID):
        pass

    def toApp(self, message, sessionID):
        pass

    def fromApp(self, message, sessionID):
        pass


def _write_cfg():
    cfg = (
        "[DEFAULT]\n"
        "ConnectionType=initiator\n"
        "HeartBtInt=30\n"
        "SenderCompID=INITIATOR\n"
        "TargetCompID=ACCEPTOR\n"
        "ResetOnLogon=Y\n"
        "ResetOnDisconnect=Y\n"
        "\n"
        "[SESSION]\n"
        "BeginString=FIX.4.4\n"
        f"SocketConnectHost=127.0.0.1\n"
        f"SocketConnectPort={FIX_PORT}\n"
    )
    f = tempfile.NamedTemporaryFile(mode="w", suffix=".cfg", delete=False)
    f.write(cfg)
    f.close()
    return f.name


def before_scenario(context, scenario):
    cfg_path = _write_cfg()
    settings = fix.SessionSettings(cfg_path)
    context.app = HarnessApp()
    store = fix.MemoryStoreFactory(settings)
    log = fix.ScreenLogFactory(settings)
    context.initiator = fix.SocketInitiator(context.app, store, log, settings)
    context.initiator.start()


def after_scenario(context, scenario):
    context.initiator.stop()

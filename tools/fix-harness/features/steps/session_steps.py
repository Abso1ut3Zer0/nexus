import os
import tempfile
import threading
import time

import quickfix as fix
import quickfix44 as fix44
from behave import given, when, then

FIX_PORT = int(os.environ.get("FIX_PORT", "9878"))


class HarnessApp(fix.Application):
    def __init__(self):
        super().__init__()
        self.logon_event = threading.Event()
        self.logout_event = threading.Event()
        self.heartbeat_event = threading.Event()
        self.last_heartbeat_req_id = None
        self.session_id = None

    def onCreate(self, sessionID):
        pass

    def onLogon(self, sessionID):
        self.session_id = sessionID
        self.logout_event.clear()
        self.logon_event.set()

    def onLogout(self, sessionID):
        self.logon_event.clear()
        self.logout_event.set()

    def toAdmin(self, message, sessionID):
        pass

    def fromAdmin(self, message, sessionID):
        msg_type = fix.MsgType()
        message.getHeader().getField(msg_type)
        if msg_type.getValue() == fix.MsgType_Heartbeat:
            try:
                req_id = fix.TestReqID()
                message.getField(req_id)
                self.last_heartbeat_req_id = req_id.getValue()
            except fix.FieldNotFound:
                pass
            self.heartbeat_event.set()

    def toApp(self, message, sessionID):
        pass

    def fromApp(self, message, sessionID):
        pass


def _make_cfg(sender, target, port):
    cfg = (
        "[DEFAULT]\n"
        "ConnectionType=initiator\n"
        "HeartBtInt=30\n"
        f"SenderCompID={sender}\n"
        f"TargetCompID={target}\n"
        "ResetOnLogon=Y\n"
        "ResetOnDisconnect=Y\n"
        "\n"
        "[SESSION]\n"
        "BeginString=FIX.4.4\n"
        "SocketConnectHost=127.0.0.1\n"
        f"SocketConnectPort={port}\n"
    )
    f = tempfile.NamedTemporaryFile(mode="w", suffix=".cfg", delete=False)
    f.write(cfg)
    f.close()
    return f.name


def _start_initiator(context):
    cfg_path = _make_cfg(context.sender, context.target, FIX_PORT)
    settings = fix.SessionSettings(cfg_path)
    context.app = HarnessApp()
    store = fix.MemoryStoreFactory(settings)
    log = fix.ScreenLogFactory(settings)
    context.initiator = fix.SocketInitiator(context.app, store, log, settings)
    context.initiator.start()


@given("a FIX 4.4 session with sender {sender} and target {target}")
def step_session_config(context, sender, target):
    context.sender = sender
    context.target = target


@when("the harness connects and sends Logon")
def step_send_logon(context):
    _start_initiator(context)


@then("the engine replies with Logon")
def step_logon_reply(context):
    assert context.app.logon_event.wait(timeout=10), \
        "engine did not reply with Logon within 10s"


@then("the session is active")
def step_session_active(context):
    assert context.app.session_id is not None


@when("the harness sends Logout")
def step_send_logout(context):
    fix.Session.sendToTarget(fix44.Logout(), context.app.session_id)


@then("the session ends cleanly")
def step_session_ends(context):
    assert context.app.logout_event.wait(timeout=10), \
        "engine did not acknowledge Logout within 10s"


@when('the harness sends a TestRequest with id "{req_id}"')
def step_send_test_request(context, req_id):
    context.app.heartbeat_event.clear()
    context.app.last_heartbeat_req_id = None
    msg = fix44.TestRequest()
    msg.setField(fix.TestReqID(req_id))
    fix.Session.sendToTarget(msg, context.app.session_id)


@then('the engine replies with Heartbeat echoing "{req_id}"')
def step_heartbeat_echo(context, req_id):
    assert context.app.heartbeat_event.wait(timeout=10), \
        "engine did not reply with Heartbeat within 10s"
    assert context.app.last_heartbeat_req_id == req_id, \
        f"expected TestReqID {req_id!r}, got {context.app.last_heartbeat_req_id!r}"


@when("the harness disconnects and reconnects with ResetSeqNumFlag")
def step_reconnect_reset(context):
    context.initiator.stop()
    context.app.logon_event.clear()
    time.sleep(0.5)
    _start_initiator(context)

from behave import given, when, then


@given("a FIX 4.4 session with sender INITIATOR and target ACCEPTOR")
def step_session_config(context):
    pass


@when("the harness connects and sends Logon")
def step_send_logon(context):
    pass


@then("the engine replies with Logon")
def step_logon_reply(context):
    assert context.app.logon_event.wait(timeout=10), \
        "engine did not reply with Logon within 10s"


@then("the session is active")
def step_session_active(context):
    assert context.app.session_id is not None

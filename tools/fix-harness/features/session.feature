# Local-only smoke test: drives the engine with the quickfix Python client.
# Not gated in CI because quickfix 1.15.1 segfaults on interpreter shutdown
# (exit 139) even when every scenario passes. Run manually via tools/fix-harness.
Feature: FIX session management

  Scenario: valid logon is accepted
    Given a FIX 4.4 session with sender INITIATOR and target ACCEPTOR
    When the harness connects and sends Logon
    Then the engine replies with Logon
    And the session is active

  Scenario: clean logout
    Given a FIX 4.4 session with sender INITIATOR and target ACCEPTOR
    When the harness connects and sends Logon
    Then the engine replies with Logon
    When the harness sends Logout
    Then the session ends cleanly

  Scenario: heartbeat exchange
    Given a FIX 4.4 session with sender INITIATOR and target ACCEPTOR
    When the harness connects and sends Logon
    Then the engine replies with Logon
    When the harness sends a TestRequest with id "TC-1"
    Then the engine replies with Heartbeat echoing "TC-1"

  Scenario: sequence reset via reconnect
    Given a FIX 4.4 session with sender INITIATOR and target ACCEPTOR
    When the harness connects and sends Logon
    Then the engine replies with Logon
    When the harness disconnects and reconnects with ResetSeqNumFlag
    Then the engine replies with Logon
    And the session is active

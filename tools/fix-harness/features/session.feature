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

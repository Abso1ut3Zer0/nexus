Feature: FIX session management

  Scenario: valid logon is accepted
    Given a FIX 4.4 session with sender INITIATOR and target ACCEPTOR
    When the harness connects and sends Logon
    Then the engine replies with Logon
    And the session is active

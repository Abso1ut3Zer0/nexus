Feature: FIX session adversarial input

  Scenario: bad checksum is ignored, session survives (E3)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with a bad checksum
    And the peer sends a TestRequest
    Then the engine replies with Heartbeat

  Scenario: lying BodyLength is ignored, session survives (E3)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with BodyLength 5
    And the peer sends a TestRequest
    Then the engine replies with Heartbeat

  Scenario: garbage framing is ignored, session survives (E4)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends garbage bytes
    And the peer sends a TestRequest
    Then the engine replies with Heartbeat

  Scenario: zero seqnum is rejected (E5)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with seqnum 0
    Then the engine closes the connection

  Scenario: duplicate seqnum is rejected (E5)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with seqnum 1
    Then the engine closes the connection

  Scenario: unbounded ResendRequest is clamped, not crashed (E2)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a ResendRequest with EndSeqNo 0
    Then the engine replies with SequenceReset

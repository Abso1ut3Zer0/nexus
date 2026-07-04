Feature: FIX session adversarial input

  Scenario: bad checksum is rejected (E3)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with a bad checksum
    Then the engine closes the connection

  Scenario: lying BodyLength causes disconnect (E3)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer performs a Logon handshake
    And the peer sends a Heartbeat with BodyLength 5
    Then the engine closes the connection

  Scenario: garbage framing is rejected (E4)
    Given a raw FIX 4.4 peer connects to the harness
    When the peer sends garbage bytes
    Then the engine closes the connection

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

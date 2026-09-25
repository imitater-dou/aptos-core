-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import Lean

/-- The heartbeat budget of a generated verification theorem, in the same
thousands-of-heartbeats units as `maxHeartbeats`. A target that does not
verify fails within it rather than searching without bound; the default
is the check driver's cap, which every checked target meets, and a target
that needs more raises it for itself. -/
register_option leaner.verifyHeartbeats : Nat := {
  defValue := 180000
  descr := "heartbeat budget of a generated verification theorem (thousands)"
}

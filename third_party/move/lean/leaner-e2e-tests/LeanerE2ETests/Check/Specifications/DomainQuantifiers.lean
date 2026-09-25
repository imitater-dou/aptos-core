-- Copyright © Aptos Foundation
-- SPDX-License-Identifier: Apache-2.0

import LeanerE2ETests.CheckSupport

/-! Quantifiers over a range and over a vector. A range binds the integers
from its lower bound below its upper bound; a vector, as in the Move Prover,
binds the element at each index below its length. -/

leaner module 0x49::quantifiers where
  fun below(n : u64) -> u64 := n

  spec below where
    ensures ∀ (i in 0 .. n), i < result
    ensures ∀ (i in n .. n), false
    ensures ∃ (i in 0 .. n), i >= result -- error: no index of the range reaches its bound

  fun length_of(v : &Vector<u64>) -> u64 := v.length

  spec length_of where
    ensures ∀ (y in v), y <= MAX_U64 || result > 0
    ensures ∃ (y in v), true -- error: an empty vector has no element

// Copyright © Aptos Foundation
// SPDX-License-Identifier: Apache-2.0

// A function-typed parameter may modify the memory its `modifies_of` frame declares, directly
// or through an opaque callee; `modifies_of<f> *` covers any memory.

module 0x42::fun_param_wildcard_frame {
    struct R has key { value: u64 }

    /// Must fail: `fv` may change `R[a]`.
    public fun read_call_read(fv: |address| has drop, a: address): bool acquires R {
        let before = R[a].value;
        fv(a);
        R[a].value == before
    }
    spec read_call_read {
        modifies_of<fv> *;
        requires exists<R>(a);
        ensures result;
    }

    /// Must fail: `fv` may change `R[a]`.
    public fun value_unchanged(fv: |address| has drop, a: address) {
        fv(a);
    }
    spec value_unchanged {
        modifies_of<fv> *;
        requires exists<R>(a);
        ensures R[a].value == old(R[a].value);
    }

    /// Must fail: `fv` may remove `R[a]`.
    public fun still_exists(fv: |address| has drop, a: address) {
        fv(a);
    }
    spec still_exists {
        modifies_of<fv> *;
        requires exists<R>(a);
        ensures exists<R>(a);
    }

    fun forward(fv: |address| has drop, a: address) {
        fv(a);
    }
    spec forward {
        pragma opaque;
        modifies_of<fv> *;
        ensures ensures_of<fv>(a);
        aborts_if aborts_of<fv>(a);
    }

    /// Must fail: the opaque `forward` passes the wildcard on.
    public fun forwarded(fv: |address| has drop, a: address) {
        forward(fv, a);
    }
    spec forwarded {
        modifies_of<fv> *;
        requires exists<R>(a);
        ensures R[a].value == old(R[a].value);
    }

    /// Must verify: the effect of `fv` is described by its behavioral predicates.
    public fun forwarded_behavior(fv: |address| has drop, a: address) {
        forward(fv, a);
    }
    spec forwarded_behavior {
        modifies_of<fv> *;
        ensures ensures_of<fv>(a);
        aborts_if aborts_of<fv>(a);
    }

    fun forward_at(fv: |address| has drop, a: address) {
        fv(a);
    }
    spec forward_at {
        pragma opaque;
        modifies_of<fv>(x: address) R[x];
        ensures ensures_of<fv>(a);
        aborts_if aborts_of<fv>(a);
    }

    /// Must fail: the opaque `forward_at` passes the addressed frame on.
    public fun forwarded_at(fv: |address| has drop, a: address) {
        forward_at(fv, a);
    }
    spec forwarded_at {
        modifies_of<fv>(x: address) R[x];
        requires exists<R>(a);
        ensures R[a].value == old(R[a].value);
    }

    /// Must fail: an addressed frame allows `R[a]` to change.
    public fun addressed(fv: |address| has drop, a: address) {
        fv(a);
    }
    spec addressed {
        modifies_of<fv>(x: address) R[x];
        requires exists<R>(a);
        ensures R[a].value == old(R[a].value);
    }
}

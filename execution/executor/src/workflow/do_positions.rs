// Copyright (c) Aptos Foundation
// Licensed pursuant to the Innovation-Enabling Source Code License, available at https://github.com/aptos-labs/aptos-core/blob/main/LICENSE

//! Per-chunk extension of the native position index.
//!
//! Called from `DoGetExecutionOutput` beside `result_state`, the main-state
//! value it is the counterpart of, so a chunk's overlay lands in
//! `ExecutionOutput` and exists before the next chunk's VM reads positions.

use crate::metrics::OTHER_TIMERS;
use anyhow::Result;
use aptos_executor_types::transactions_with_output::TransactionsToKeep;
use aptos_metrics_core::TimerHelper;
use aptos_storage_interface::state_store::{
    positions::{position_key_of, LedgerPositions, PositionWrites},
    state_with_summary::LedgerWithSummary,
};
use aptos_types::{state_store::native_position::NativePosition, transaction::Version};

pub struct DoPositions;

impl DoPositions {
    /// Pushes one layer per shard at the block's last version.
    ///
    /// Not gated on `compute_trading_native_state_roots`, unlike the
    /// JMT-side summary — that flag only affects the consensus root.
    /// `None` means the feature is off; writes are empty then, and
    /// non-empty writes without a parent is a wiring bug, so it errors.
    pub fn run(
        to_commit: &TransactionsToKeep,
        first_version: Version,
        parent: Option<&LedgerPositions>,
    ) -> Result<Option<LedgerPositions>> {
        let _timer = OTHER_TIMERS.timer_with(&["do_positions"]);

        let num_txns = to_commit.len();

        // Per transaction so the chunk can be split at its state checkpoint.
        // The layer build resolves latest-wins, so only arrival order matters.
        let mut per_txn: Vec<PositionWrites> = Vec::with_capacity(num_txns);
        for output in &to_commit.transaction_outputs {
            let mut writes = PositionWrites::new();
            for (key, op) in output.write_set().native_position_iter() {
                let position_key = position_key_of(key).map_err(anyhow::Error::from)?;
                let value = op
                    .as_write_op()
                    .as_state_value_opt()
                    .map(|sv| NativePosition::deserialize(sv.bytes()))
                    .transpose()
                    .map_err(|e| {
                        anyhow::anyhow!("native position value failed to decode at execution: {e}")
                    })?;
                writes.push((position_key, value));
            }
            per_txn.push(writes);
        }

        // No parent means the feature is off, or the caller only verifies and
        // never commits. Fabricating a family would orphan the cold-loaded
        // data; `commit_native_position` rebuilds from the chunk's own writes
        // if a chunk ever reaches it without one.
        let Some(parent) = parent else {
            return Ok(None);
        };

        let parent_latest = parent.latest().clone();
        let parent_last_checkpoint = parent.last_checkpoint().clone();

        if num_txns == 0 {
            return Ok(Some(LedgerWithSummary::from_latest_and_last_checkpoint(
                parent_latest,
                parent_last_checkpoint,
            )));
        }

        let collect = |range: std::ops::Range<usize>| -> PositionWrites {
            per_txn[range].iter().flatten().cloned().collect()
        };

        // Split at the checkpoint, as the JMT side and main state do, or
        // post-checkpoint writes fold into it.
        let last_version = first_version + num_txns as u64 - 1;
        let (new_latest, new_last_checkpoint) =
            match to_commit.state_update_refs().last_inner_checkpoint_index() {
                Some(ci) if ci + 1 == num_txns => {
                    let new_ckpt = parent_latest.extend(last_version, collect(0..num_txns));
                    (new_ckpt.clone(), new_ckpt)
                },
                Some(ci) => {
                    let new_ckpt =
                        parent_latest.extend(first_version + ci as u64, collect(0..ci + 1));
                    let new_latest = new_ckpt.extend(last_version, collect(ci + 1..num_txns));
                    (new_latest, new_ckpt)
                },
                None => (
                    parent_latest.extend(last_version, collect(0..num_txns)),
                    parent_last_checkpoint,
                ),
            };

        Ok(Some(LedgerWithSummary::from_latest_and_last_checkpoint(
            new_latest,
            new_last_checkpoint,
        )))
    }
}

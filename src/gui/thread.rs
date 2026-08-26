// SPDX-License-Identifier: MPL-2.0
//
// Copyright © 2026 RemasteredArch
//
// This Source Code Form is subject to the terms of the Mozilla Public License, version 2.0. If a
// copy of the Mozilla Public License was not distributed with this file, You can obtain one at
// <https://mozilla.org/MPL/2.0/>.

use std::{sync::Arc, thread::JoinHandle};

use anyhow::Context;
use iced::{
    Task,
    futures::{lock::Mutex, task::AtomicWaker},
};

use super::Message;

pub struct Thread<T> {
    result: Arc<Mutex<Option<T>>>,
    waker: Arc<AtomicWaker>,
    /// The handle of the thread owned by this struct. Always [`Some`] until a [`Future::poll`]
    /// notices it has finished and [takes][`Option::take`] it to check for an error.
    handle: Option<JoinHandle<()>>,
}

impl<T: Send + 'static> Thread<T> {
    pub fn spawn<F: FnOnce() -> T + Send + 'static>(
        name: impl Into<String>,
        func: F,
    ) -> std::io::Result<Self> {
        let result = Arc::new(Mutex::new(None));
        let waker: Arc<AtomicWaker> = Arc::new(AtomicWaker::new());

        let handle = std::thread::Builder::new().name(name.into()).spawn({
            let mut result = result.try_lock_owned().unwrap();
            let waker = waker.clone();
            move || {
                *result = Some(func());
                drop(result);
                waker.wake();
            }
        })?;

        Ok(Self {
            result,
            waker,
            handle: Some(handle),
        })
    }
}

impl<T> Future for Thread<T> {
    type Output = std::thread::Result<T>;

    fn poll(
        mut self: std::pin::Pin<&mut Self>,
        cx: &mut std::task::Context<'_>,
    ) -> std::task::Poll<Self::Output> {
        if self.handle.as_ref().is_some_and(JoinHandle::is_finished)
            && let Err(err) = self.handle.take().unwrap().join()
        {
            return std::task::Poll::Ready(Err(err));
        }

        if let Some(mut lock) = self.result.try_lock() {
            let result = lock
                .take()
                .expect("a `Future` should not be polled after finishing");

            std::task::Poll::Ready(Ok(result))
        } else {
            self.waker.register(cx.waker());
            std::task::Poll::Pending
        }
    }
}

pub fn scan_in_thread() -> Task<Message> {
    let maybe_thread = Thread::<anyhow::Result<wf_inv_auth_scanning::Login>>::spawn(
        "Credential Scanner",
        crate::scan,
    );

    let task: Task<anyhow::Result<_>> = match maybe_thread {
        Ok(thread) => Task::perform(thread, |result| {
            result
                .map_err(|_| anyhow::anyhow!("credential scanner thread panicked (error unknown)"))
                .flatten()
        }),
        Err(err) => Task::done(Err(anyhow::anyhow!(
            "failed to start credential scanner thread: {err}",
        ))),
    };

    task.map(|result| {
        result
            .context("failed to scan for login credentials")
            .map_err(Arc::new)
    })
    .map(Message::FinishedScanning)
}

pub fn fetch_in_thread(login: wf_inv_auth_scanning::Login) -> Task<Message> {
    let maybe_thread =
        Thread::<anyhow::Result<String>>::spawn("Inventory Fetcher", move || crate::fetch(&login));

    let task: Task<anyhow::Result<_>> = match maybe_thread {
        Ok(thread) => Task::perform(thread, |result| {
            result
                .map_err(|_| anyhow::anyhow!("inventory fetcher thread panicked (error unknown)"))
                .flatten()
        }),
        Err(err) => Task::done(Err(anyhow::anyhow!(
            "failed to start inventory fetcher thread: {err}",
        ))),
    };

    task.map(|result| {
        result
            .context("failed to fetch inventory contents")
            .map_err(Arc::new)
    })
    .map(Message::FinishedFetching)
}

pub fn parse_inventory_in_thread(
    display_settings: crate::settings::DisplayArgs,
    parse_args: crate::settings::ParseArgs,
    inventory_json: impl std::io::Read + Send + 'static,
) -> Task<Message> {
    let maybe_thread = {
        Thread::<anyhow::Result<crate::table::Table>>::spawn("Inventory Parser", move || {
            let items = crate::parse(parse_args, inventory_json)?;

            let print_args = crate::settings::PrintArgs {
                display_args: display_settings,
                table_column_separator: None,
                table_header_separator: None,
            };

            let table = if print_args.display_args.group_subtypes {
                crate::to_tsv_summary(print_args, items)
            } else {
                crate::to_table(print_args, &items)?
            };

            Ok(table)
        })
    };

    let task: Task<anyhow::Result<_>> = match maybe_thread {
        Ok(thread) => Task::perform(thread, |result| {
            result
                .map_err(|_| anyhow::anyhow!("parser thread panicked (error unknown)"))
                .flatten()
        }),
        Err(err) => Task::done(Err(anyhow::anyhow!(
            "failed to start inventory parser thread: {err}",
        ))),
    };

    task.map(|result| {
        result
            .context("failed to parse inventory data")
            .map_err(Arc::new)
    })
    .map(Message::FinishedParsing)
}

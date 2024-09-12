# Crontab Expression Parser and Driver

[![Crates.io][crates-badge]][crates-url]
[![Documentation][docs-badge]][docs-url]
[![MSRV 1.75][msrv-badge]](https://www.whatrustisit.com)
[![Apache 2.0 licensed][license-badge]][license-url]
[![Build Status][actions-badge]][actions-url]

[crates-badge]: https://img.shields.io/crates/v/cronexpr.svg
[crates-url]: https://crates.io/crates/cronexpr
[docs-badge]: https://docs.rs/cronexpr/badge.svg
[msrv-badge]: https://img.shields.io/badge/MSRV-1.75-green?logo=rust
[docs-url]: https://docs.rs/cronexpr
[license-badge]: https://img.shields.io/crates/l/cronexpr
[license-url]: LICENSE
[actions-badge]: https://github.com/tisonkun/cronexpr/workflows/CI/badge.svg
[actions-url]:https://github.com/tisonkun/cronexpr/actions?query=workflow%3ACI

## Overview

This library provides functionalities to calculate the next timestamp matching a given crontab pattern.

## Usage

```shell
cargo add cronexpr
```

```rust
fn main() {
    // with jiff timestamp
    let timestamp = jiff::Timestamp::from_str("2024-01-01T00:00:00+08:00").unwrap();
    let driver = cronexpr::Driver::with_timestamp("0 0 1 1 * Asia/Shanghai", timestamp).unwrap();
    assert_eq!(driver.find_next_timestamp().unwrap().as_millisecond(), 1735660800000);

    // for compatibility, bridge by timestamp milliseconds (crontab support at most second level so it's fine)
    let driver = cronexpr::Driver::with_timestamp_millis("2 4 * * * Asia/Shanghai", 1704038400000).unwrap();
    assert_eq!(driver.find_next_timestamp_millis().unwrap(), 1704052920000);

    // can also be used as an iterator
    let mut driver = cronexpr::Driver::with_timestamp_millis("2 4 * * * Asia/Shanghai", 1704038400000).unwrap();
    assert_eq!(driver.next_timestamp_millis().unwrap(), 1704052920000);
    assert_eq!(driver.next_timestamp_millis().unwrap(), 1704139320000);
    assert_eq!(driver.next_timestamp_millis().unwrap(), 1704225720000);
}
```

# `wf_inv`

Scan a running Warframe process for API credentials,
fetch the inventory for the account,
parse it for tradable items,
and fetch their recent pricing data.

## Stability

Until it is published on <https://crates.io>,
this library make no guarantees of stability.
This is code I will write, update, and break whenever I feel the need or desire to.
That being said,
you are encouraged to request features or make contributions!

A part of these breaking changes includes possible name changes,
if `wf_inv` is ever to be registered by someone else
or I otherwise decide there's a better name.

### MSRV

`wf_inv` supports only the latest stable Rust.
Older version _may_ work, but are not tested.
MSRV naturally being bumped as new stable versions release
is not considered a breaking change.

## Looking forwards

There's a few features I'm looking to add in the future.

- Better code quality.
  Lots of `wf_inv`'s code is internally undocumented,
  and specifically `wf_inv_auth_scanning` has lots of unjustified unsafe code.
- A web service.
  Currently, `wf_inv` uses an undocumented API for pricing data
  because the actual warframe.market API has too aggressive of rate limiting for a CLI to reasonably use it directly,
  but running a web service to aggregate data daily is viable.
  Having my own is better for a number of reasons,
  but I am prioritizing finishing the CLI before I get to that.

## License

`wf_inv` is licensed under the Mozilla Public License,
version 2.0 or (as the license stipulates) any later version.
A copy of the license should be distributed with `wf_inv`,
located at [`LICENSE`](./LICENSE),
or you can obtain one at <https://mozilla.org/MPL/2.0/>.

### Credits

The memory scanning behavior of `wf_inv_auth_scanning` is partly based on
Sainan's [`warframe-api-helper`](https://github.com/Sainan/warframe-api-helper/tree/38bb942f7131cebf8877b1cea38355b486baf18a).

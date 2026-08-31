# `wf_inv`

Scan a running Warframe process for API credentials,
fetch the inventory for the account,
parse it for tradable items,
and fetch their recent pricing data.
It features both a CLI and an optional (and currently experimental) GUI.

To minimize API usage,
please avoid fetching inventory contents often
(i.e., do not scan & parse often).
Instead, to save the contents to a file,
at which point you may parse it as many times as you see fit.

`wf_inv` is not an official project of warframe.market or Warframe.
It is not approved by or associated with the 42Bytes team or Digital Extremes Ltd.

## Stability

Until it is published on <https://crates.io>,
this library make no guarantees of stability
other than [Semantic Versioning](https://semver.org/).
This is code I will write, update, and break whenever I feel the need or desire to.
That being said,
you are encouraged to request features or make contributions!

A part of these breaking changes includes possible name changes,
if `wf_inv` is ever to be registered by someone else
or I otherwise decide there's a better name.

It's not clear where the boundaries for Semantic Versioning lie for the GUI.
It's relatively straightforward to treat the CLI as an API,
but the GUI is largely exempt from this.
I expect that most changes will qualify as minor or patch changes,
do not rely on the GUI being unchanging.

### MSRV

`wf_inv` supports only the latest stable Rust.
Older versions _may_ work, but are not tested.
MSRV naturally being bumped as new stable versions release
is not considered a breaking change.

## Looking forward

There are a few features I'm looking to add in the future:

- Better code quality.
  Lots of `wf_inv`'s code is internally undocumented,
  the GUI code is in desperate need of refactoring,
  and specifically `wf_inv_auth_scanning` has lots of unjustified unsafe code.
- A web service.
  Currently, `wf_inv` uses an undocumented API for pricing data
  because the actual warframe.market API has too aggressive of rate limiting for a CLI to reasonably use it directly,
  but running a web service to aggregate data daily is viable.
  Having my own is better for a number of reasons,
  but I am prioritizing finishing the CLI before I get to that.
  - It's unlikely that I would actually make my own scraper,
    as the warframe.market developers specifically requested that such projects use the data source I use instead of scraping themselves.
    It's still worth doing, however, because I could pre-parse server side
    and update data sources without having to issue a full code update.
- Better accessibility in the GUI.
  Currently, it features no keyboard controls
  and I have no idea how it interacts with screen readers.
- Better table rendering in the GUI.
  As of right now tables are rendered statically and fully,
  causing performance an issues and preventing the user from changing sorting on demand.
- A Linux build.
  `wf_inv` is currently only built for Windows
  because `wf_inv_auth_scanning` relies on direct use of Windows APIs
  to find processes and scan memory.
  Other platforms have similar APIs that I could use and Warframe works well under Proton,
  but I haven't developed a port because I simply don't game on Linux at all.
  It's also possible that `wf_inv` simply just works under Wine,
  I haven't tested it yet.
  - If a Linux port would be useful to you, please let me know!

## License

`wf_inv` is licensed under the Mozilla Public License,
version 2.0 or (as the license stipulates) any later version.
A copy of the license should be distributed with `wf_inv`,
located at [`LICENSE`](./LICENSE),
or you can obtain one at <https://mozilla.org/MPL/2.0/>.

### Credits

The memory scanning behavior of `wf_inv_auth_scanning` is partly based on
Sainan's [`warframe-api-helper`](https://github.com/Sainan/warframe-api-helper/tree/38bb942f7131cebf8877b1cea38355b486baf18a).

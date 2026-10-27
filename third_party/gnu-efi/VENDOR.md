# gnu-efi (vendored headers)

| | |
|---|---|
| Upstream | https://github.com/ncroxon/gnu-efi |
| Release | 4.0.4 (2025-12-06), tag commit `37cd8f069bde6715eebdc5e38a8f15ee6de5edcf` |
| Archive | https://github.com/ncroxon/gnu-efi/archive/refs/tags/4.0.4.tar.gz |
| Archive SHA-256 | `40b61e842a4efcbf80f3e53b2f220c044e8cfe46eb4dd6396c83b751240b1c0d` |
| Fetched | 2026-10-24 |
| Local patches | none: every file is byte-identical to the archive |

## What is copied

Headers only, from `inc/`:
- the top-level `inc/*.h`, `inc/Makefile`;
- `inc/x86_64/`, `inc/aarch64/` (the two ISAs we build);
- `inc/internal/`, `inc/protocol/`, `inc/legacy/`.

Plus `LICENSE` and `licenses/LICENSE.efilib`, `LICENSE.BSD-3-Clause`, `LICENSE.edk2`.

## What is deliberately not copied

- `gnuefi/` (crt0, linker scripts, self-relocation: the ELF->PE glue). Not needed: we link PE32+ images directly with `lld-link`. Licensed GPL-2.0-or-later OR BSD-3-Clause; left out to keep the tree to the plain BSD parts.
- `lib/` (libefi helpers). BSD-3-Clause, but unused: the runtime calls firmware services through the system table directly.
- `inc/subst/elf.h` (LGPL-2.1-or-later), `apps/`, `tests/` (GPL-2.0-or-later), `docs/`, the other ISAs' `inc/<arch>/` directories.

## Licence

Per upstream `LICENSE`: `inc/` is BSD-3-Clause (`licenses/LICENSE.efilib`). Within the copied files:
- most carry Intel's 1998–2000 copyright under that licence;
- `inc/efishell.h` and a few protocol headers are from EDK II, BSD-2-Clause-Patent (`licenses/LICENSE.edk2`);
- `inc/aarch64/efibind.h` (Linaro) is BSD-style with a GPL-2.0-or-later alternative; we use it under the BSD terms.

No copied file is GPL- or LGPL-only (checked file by file on import). Kraken itself is MIT.

## Updating

Fetch the new release archive, record its tag commit and SHA-256 here, replace exactly the paths listed above, re-run the per-file licence check, and rebuild with `runtime/efi/build.sh`.

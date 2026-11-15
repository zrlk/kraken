#!/usr/bin/env bash
# Runs qemu_window.sh ISA (the release image) without a debugger, for VS
# Code: Ctrl+F5 on the "debug" configuration runs it directly in the
# terminal, and the "run" configuration (F5 or Ctrl+F5) runs it as
# /bin/bash's argument under gdb.
#
# Usage: runtime/efi/run_nodebug.sh [x64|a64]   (default x64)
# gdb traces only the process it starts, not that process's children, so
# qemu_window.sh runs in a child, free of gdb. Stopping can kill this script
# without a chance to clean up (SIGKILL), so the child watches it and closes
# QEMU when it is gone.
set -u

parent=$$
(
  "$(dirname "$0")/qemu_window.sh" "${1:-x64}" &
  q=$!
  while kill -0 "$parent" 2>/dev/null && kill -0 "$q" 2>/dev/null; do sleep 1; done
  kill "$q" 2>/dev/null  # through WSL interop, this closes the Windows QEMU too
) &
wait $!

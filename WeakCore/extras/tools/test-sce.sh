#!/bin/bash
# test-sce.sh — tools/sce end to end (UnElab M3a, M3b, M3d): the real command, files and exit codes.
# SceTest.lean covers the pipeline itself (pure, every message); this checks the shell around it: arguments
# through the environment, reading imports from disk (-I), -o, the I/O error text, stdout/stderr, exit codes,
# the live stage's report and exit code, --live-proof writing and building its instance file,
# and that elaborating Sce.lean without arguments (as a build does) does nothing.
# Usage: WM_BUILD=build WM_LEAN=lean tools/test-sce.sh     (about 1 minute: ~12 s per run)
cd "$(dirname "$0")/.." || exit 1
B="${WM_BUILD:-${BUILD:-build}}"
L="${WM_LEAN:-${LEAN:-$HOME/.elan/bin/lean}}"
export WM_BUILD="$B" WM_LEAN="$L"
T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT
fail=0
bad() { echo "FAIL: test-sce: $*"; fail=1; }

mkdir -p "$T/lib"
printf 'def inc(x : Int) : Int =\n  ret (x + 1)\n' > "$T/lib/Q.u"
printf 'import Q\ndef main(u : Unit) : Int =\n  tail inc(41)\n' > "$T/a.u"
printf 'def f(x : Int) : Int =\n  let y = load acq x\n  ret y\n' > "$T/chk.u"
printf 'scenario S = { setup = init(()) ; threads = [spin(())] ; depth = 60 ; live = 0 }\ndef init(u : Unit) : Ptr pub Int =\n  let z = zero[Int]\n  let o = new z\n  let c = publish o\n  ret c\nlive[S] def spin(c : Ptr pub Int) : Int =\n  let d = load acq c\n  if d = 1 then\n    ret 0\n  else\n    tail spin(c)\n' > "$T/live.u"
printf 'live def f{r}(w : Ptr pub Word[r, <k! ; 0->0+1 ; robust, epoch>]) : Unit =\n  ret ()\n' > "$T/ep.u"

# 1. --help: exit 0, the slogan last after a blank line
out=$(tools/sce --help 2>&1); rc=$?
[ $rc -eq 0 ] || bad "--help: exit $rc"
[ "$(printf '%s\n' "$out" | tail -2 | head -1)" = "" ] && [ "$(printf '%s\n' "$out" | tail -1)" = "Share and enjoy!" ] \
  || bad "--help: last lines are not a blank line and 'Share and enjoy!'"

# 2. -I and -o: exit 0, nothing on stdout, the file starts with the header and holds both blocks
out=$(tools/sce -I "$T/lib" -o "$T/a.w" "$T/a.u" 2>&1); rc=$?
[ $rc -eq 0 ] || bad "a.u: exit $rc: $out"
[ -z "$out" ] || bad "a.u -o: unexpected output: $out"
[ "$(head -1 "$T/a.w" 2>/dev/null)" = "-- sce: from $T/a.u" ] || bad "a.w: no header"
[ "$(awk '/^def /' "$T/a.w" 2>/dev/null | wc -l)" -eq 2 ] || bad "a.w: expected 2 blocks"

# 3. a checker error: exit 2, the diagnostic on stderr, nothing on stdout
tools/sce "$T/chk.u" >"$T/out" 2>"$T/err"; rc=$?
out=$(cat "$T/out"); err=$(cat "$T/err")
[ $rc -eq 2 ] || bad "chk.u: exit $rc"
[ -z "$out" ] || bad "chk.u: stdout not empty"
[ "$(printf '%s\n' "$err" | head -1)" = "$T/chk.u:2:11: in f: load needs a reference" ] || bad "chk.u: stderr: $err"

# 4. a missing input: exit 4, `sce: cannot read FILE: <error>`
err=$(tools/sce "$T/none.u" 2>&1); rc=$?
[ $rc -eq 4 ] || bad "none.u: exit $rc"
case "$err" in "sce: cannot read $T/none.u: "*) ;; *) bad "none.u: $err" ;; esac

# 5. a fair livelock where none is expected: exit 5, nothing on stdout; the report and the error on stderr
tools/sce "$T/live.u" >"$T/out" 2>"$T/err"; rc=$?
out=$(cat "$T/out"); err=$(cat "$T/err")
[ $rc -eq 5 ] || bad "live.u: exit $rc"
[ -z "$out" ] || bad "live.u: stdout not empty"
case "$err" in *"thread 0 [spins] at $T/live.u:12:5"*) ;; *) bad "live.u: no placed thread: $err" ;; esac
[ "$(printf '%s\n' "$err" | awk '/: live: /' | head -1)" = "$T/live.u:1:10: live: expected 0 fair livelock(s), found 1" ] \
  || bad "live.u: stderr: $err"

# 6. --live-proof: exit 0; the instance is written next to the input, built by lean, then reported
tools/sce --live-proof -o "$T/ep.w" "$T/ep.u" >"$T/out" 2>"$T/err"; rc=$?
out=$(cat "$T/out"); err=$(cat "$T/err")
[ $rc -eq 0 ] || bad "ep.u --live-proof: exit $rc: $err"
[ -z "$out" ] || bad "ep.u --live-proof: stdout not empty"
[ "$err" = "$(printf 'live def f: PROVED (under the standard obligations)\n  re-checked in Lean: %s' "$T/ep.live.lean")" ] \
  || bad "ep.u --live-proof: stderr: $err"
[ "$(head -1 "$T/ep.live.lean" 2>/dev/null)" = "-- sce: the liveness instance of ep" ] || bad "ep.live.lean: no header"

# 8. --live-proof with a certificate (item 38): root.cert/ is written and built after the instance file; the
# certificate's PROVED lines come last, each with its re-checked line
printf 'scenario S = { setup = init(()) ; threads = [spin(()), setter(())] ; depth = 60 ; live = 0 ; cert = 1000 }\ndef init(u : Unit) : Ptr pub Int =\n  let z = zero[Int]\n  let o = new z\n  let c = publish o\n  ret c\nlive[S] def spin(c : Ptr pub Int) : Int =\n  let d = load acq c\n  if d = 1 then\n    ret 0\n  else\n    tail spin(c)\nlive def setter(c : Ptr pub Int) : Unit =\n  let d = store rel c 1\n  ret ()\n' > "$T/cert.u"
tools/sce --live-proof -o "$T/cert.w" "$T/cert.u" >"$T/out" 2>"$T/err"; rc=$?
err=$(cat "$T/err")
[ $rc -eq 0 ] || bad "cert.u --live-proof: exit $rc: $err"
want=$(printf '%s\n  re-checked in Lean: %s\n' \
  "live[S]: no fair livelock: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm)" "$T/cert.cert/S/main.lean" \
  "live[S]: final states: exhaustive: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm)" "$T/cert.cert/S/main.lean" \
  "live[S]: every fair run reaches a final state: PROVED for promise-free runs (under the standard obligations; kernel-checked certificate; arm)" "$T/cert.cert/S/main.lean")
[ "$(printf '%s\n' "$err" | tail -6)" = "$want" ] || bad "cert.u --live-proof: stderr: $err"
[ "$(printf '%s\n' "$err" | sed -n 4p)" = "  no fair livelock: certificate checked for promise-free runs (compiled evaluation)" ] \
  || bad "cert.u --live-proof: no mode-A line: $err"
[ -f "$T/cert.cert/S/main.olean" ] || bad "cert.u --live-proof: main.lean not built"

# 7. a build of Sce.lean (no SCE_ARGC) does nothing
out=$(env -u SCE_ARGC LEAN_PATH="$B" "$L" --load-dynlib="$B/libwm.so" Sce.lean 2>&1); rc=$?
[ $rc -eq 0 ] && [ -z "$out" ] || bad "Sce.lean without arguments: exit $rc, output: $out"

[ $fail -eq 0 ] && echo "test-sce: 8 runs OK"
exit $fail

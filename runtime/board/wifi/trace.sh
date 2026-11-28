#!/usr/bin/env bash
# Wi-Fi driver trace on the board: what iwlwifi asks the AX101 to do.
#
# Usage: sudo ./trace.sh [--ssid NAME --psk PASSWORD] [--no-reload] [OUTDIR]
#
# With the kernel's iwlwifi trace events (text form only) it records, in
# order: a driver reload (module removed and loaded again, so the probe,
# firmware load and "alive" sequence are traced), a scan and, if --ssid is
# given, a WPA2 connection, a ping of the gateway and a disconnect. Each
# phase starts with a PHASE marker line in trace.txt.
#
# What is recorded: command ids, notification ids, frame lengths, register
# and periphery accesses with their values, interrupts and the driver's own
# messages. Not recorded: command payloads, frame contents (the
# iwlwifi_data events stay off), the scan results (only their count), the
# password, the network's name (SSID), or nmcli's output. MAC addresses do
# appear: the adapter's in dmesg, the access point's in driver messages.
#
# The reload takes Wi-Fi down for a few seconds; it never touches the
# Ethernet ports. Tracing is switched off and the buffer size restored at
# the end, also on Ctrl-C.
set -u
SSID="" PSK="" RELOAD=1 OUT=""
while [ $# -gt 0 ]; do
  case $1 in
  --ssid) SSID=$2; shift 2 ;;
  --psk) PSK=$2; shift 2 ;;
  --no-reload) RELOAD=0; shift ;;
  -h | --help) sed -n '2,22p' "$0"; exit 0 ;;
  *) OUT=$1; shift ;;
  esac
done
[ "$(id -u)" -eq 0 ] || { echo "trace.sh: run as root" >&2; exit 1; }
OUT=${OUT:-wifi-trace-$(date -u +%Y%m%d-%H%M%S)}
mkdir -p "$OUT" || exit 1
LOG=$OUT/trace.log
log() { echo "$*" | tee -a "$LOG"; }

T=/sys/kernel/tracing
[ -d "$T/events" ] || mount -t tracefs nodev "$T" 2>/dev/null
HAVE_TRACE=1
if [ ! -d "$T/events/iwlwifi" ]; then
  HAVE_TRACE=0
  log "trace.sh: no iwlwifi trace events (kernel built without CONFIG_IWLWIFI_DEVICE_TRACING?); dmesg only"
fi

ifname() {
  local d
  for d in /sys/class/net/*; do
    case $(readlink -f "$d/device/driver" 2>/dev/null) in
    */iwlwifi) basename "$d"; return 0 ;;
    esac
  done
  return 1
}
mark() {
  log "PHASE $1 $(date -u +%H:%M:%S)"
  [ $HAVE_TRACE -eq 1 ] && echo "PHASE $1" >"$T/trace_marker"
}

# The trace systems recorded (iwlwifi_data, which carries payloads, is not).
SYSTEMS="iwlwifi iwlwifi_io iwlwifi_msg iwlwifi_ucode"
OLD_BUF=""
cleanup() {
  if [ $HAVE_TRACE -eq 1 ]; then
    echo 0 >"$T/tracing_on"
    # Clears every enabled event and any pending ":mod:" request.
    echo >"$T/set_event"
    [ -n "$OLD_BUF" ] && echo "$OLD_BUF" >"$T/buffer_size_kb"
  fi
}
trap 'cleanup; exit 130' INT TERM

# Facts first (read-only).
{
  uname -a
  modinfo iwlwifi 2>&1 | awk '/^(filename|version|vermagic|firmware):/' | head -5
} >"$OUT/system.txt" 2>&1
lspci -nn -vvv -xxxx -s 00:14.3 >"$OUT/lspci-00-14.3.txt" 2>&1
dmesg | awk '/iwlwifi/' >"$OUT/dmesg-before.txt"
IF=$(ifname) || IF=""
log "trace.sh: interface ${IF:-none}"
# Without the "ssid" line: the network's name stays out of the tarball.
[ -n "$IF" ] && iw dev "$IF" info 2>&1 | awk '$1 != "ssid"' >"$OUT/iw-info.txt"
iw list >"$OUT/iw-list.txt" 2>&1

if [ $HAVE_TRACE -eq 1 ]; then
  echo 0 >"$T/tracing_on"
  OLD_BUF=$(awk '{print $1}' "$T/buffer_size_kb")
  echo 65536 >"$T/buffer_size_kb"
  echo >"$T/trace"
  for s in $SYSTEMS; do
    [ -e "$T/events/$s/enable" ] && echo 1 >"$T/events/$s/enable"
  done
  echo 1 >"$T/tracing_on"
fi

if [ $RELOAD -eq 1 ]; then
  mark reload
  [ -n "$IF" ] && nmcli dev disconnect "$IF" >/dev/null 2>&1
  # (Ubuntu's modprobe.d remove rule for iwlwifi may print a harmless
  # "rmmod: missing module name" once iwlmvm is gone.)
  modprobe -r iwlmvm iwlwifi 2>>"$LOG"
  sleep 2
  # The module's events go away with it. Ask the kernel (6.14 and later,
  # Documentation/trace/events.rst) to enable them again when it loads.
  if [ $HAVE_TRACE -eq 1 ]; then
    for s in $SYSTEMS; do
      echo "$s:*:mod:iwlwifi" >>"$T/set_event" 2>>"$LOG" ||
        log "trace.sh: cannot request $s events on load (kernel older than 6.14?)"
    done
  fi
  modprobe iwlwifi 2>>"$LOG"
  [ $HAVE_TRACE -eq 1 ] && awk '/^iwlwifi/' "$T/set_event" | sort -u >"$OUT/events-after-load.txt"
  for _ in $(seq 20); do IF=$(ifname) && break; sleep 1; done
  sleep 5
  log "trace.sh: after reload interface ${IF:-none}"
fi

if [ -n "$IF" ]; then
  mark scan
  ip link set "$IF" up 2>>"$LOG"
  n=$(iw dev "$IF" scan 2>>"$LOG" | awk '/^BSS /' | wc -l)
  log "trace.sh: scan found $n networks"
  if [ -n "$SSID" ]; then
    mark connect
    # A profile for this network that existed before is used, kept and
    # brought up again at the end; one this script creates is deleted.
    had=$(nmcli -g NAME connection show 2>/dev/null | awk -v s="$SSID" '$0 == s' | head -1)
    # After the reload NetworkManager's list of networks is empty: rescan
    # and give it time, or the connection fails at once.
    nmcli dev wifi rescan ifname "$IF" >/dev/null 2>&1
    sleep 8
    if [ -n "$had" ]; then
      err=$(nmcli --wait 40 connection up id "$SSID" ifname "$IF" 2>&1 >/dev/null)
    else
      err=$(nmcli --wait 40 dev wifi connect "$SSID" password "$PSK" ifname "$IF" 2>&1 >/dev/null)
    fi
    rc=$?
    if [ $rc -eq 0 ]; then
      log "trace.sh: connect ok"
      sleep 3
      mark ping
      gw=$(ip -4 route show dev "$IF" default | awk '{print $3; exit}')
      if [ -n "$gw" ]; then
        ping -c 10 -i 0.5 -I "$IF" "$gw" | tail -3 >>"$LOG" 2>&1
      else
        log "trace.sh: no default route on $IF"
      fi
      mark disconnect
      nmcli dev disconnect "$IF" >/dev/null 2>&1
      sleep 2
      if [ -z "$had" ]; then
        nmcli connection delete id "$SSID" >/dev/null 2>&1
      fi
    else
      # nmcli's message with the network's name replaced.
      log "trace.sh: connect failed (nmcli exit $rc): ${err//"$SSID"/<ssid>}"
    fi
  fi
  mark end
  if [ -n "$SSID" ] && [ -n "${had:-}" ]; then
    # Tracing stops at the end marker; restore the network the board was on.
    echo 0 >"$T/tracing_on" 2>/dev/null
    nmcli --wait 40 connection up id "$SSID" >/dev/null 2>&1 &&
      log "trace.sh: reconnected to the existing profile" ||
      log "trace.sh: could not bring the existing profile up again"
  fi
else
  log "trace.sh: no iwlwifi interface; nothing to scan"
fi

if [ $HAVE_TRACE -eq 1 ]; then
  echo 0 >"$T/tracing_on"
  cp "$T/trace" "$OUT/trace.txt"
  awk '/^CPU:|overrun|entries/' "$T/per_cpu/cpu0/stats" >"$OUT/trace-stats-cpu0.txt" 2>/dev/null
  for c in "$T"/per_cpu/cpu*; do
    echo "$(basename "$c") $(awk '/overrun/' "$c/stats")"
  done >"$OUT/trace-overruns.txt"
fi
cleanup
trap - INT TERM
dmesg | awk '/iwlwifi/' >"$OUT/dmesg-after.txt"
log "trace.sh: $(wc -l <"$OUT/trace.txt" 2>/dev/null || echo 0) trace lines"
tar -czf "$OUT.tar.gz" "$OUT" && log "trace.sh: wrote $OUT.tar.gz"

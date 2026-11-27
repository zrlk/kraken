# Realtek NIC facts

`facts.sh OUTDIR` collects read-only facts about every Realtek 10ec:8168
function (on the board: 01:00.0 and 02:00.0, RTL8168h, driven by r8169).
`../gfx/run_all.sh` runs it and puts the output under `nic/` in the same
tarball; it can also be run alone, as root:

    sudo ./facts.sh nic-facts

Per function (`OUTDIR/<pci address>/`) it records:

- `lspci -vvv -xxxx` (capabilities and the full 4 KiB config space) and the
  sysfs attributes `msi_irqs`, `irq`, `resource`, link speed and width;
- for each bound interface: `ethtool -i` (driver, firmware version),
  `ethtool -d` decoded and in hex, the raw register dump
  (`<if>-regs.bin`; r8169 returns the first 256 bytes of the MMIO window),
  `ethtool -S`, `-k`, `-c`, `-g`, link settings (`ethtool <if>`),
  `ip -d -s link` and the interface's `/proc/interrupts` lines.

Once for the system: kernel version, `ip -d link`, the r8169 and rtl_nic
lines of dmesg, the NIC lines of `/proc/interrupts`, r8169 module
information, and the SHA-256 of `/lib/firmware/rtl_nic/rtl8168h-2.fw` (the
firmware itself is not copied).

## Safety

The script only queries. It uses no ethtool option that changes state
(`-s`, `-K`, `-G`, `-C`, ...), never unbinds, rebinds or reloads the driver,
and never changes a link. Missing tools or permissions are written into the
output and the script continues.

## Deferred: MMIO trace of the driver

A trace of r8169's register accesses during probe (the kernel's mmiotrace
tracer) would show the initialisation sequence. It needs the driver to be
unbound and bound again on the traced port, which takes that link down. It
is not part of the kit. If it is done later, use the port you are **not**
logged in through, and only by hand.

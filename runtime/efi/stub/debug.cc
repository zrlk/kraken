/*
 * Kraken EFI stub: debugging aids (see debug.h).
 */
#include "debug.h"

#if defined(__x86_64__)
#include "x64.h"
#endif

/* Echoes the framebuffer's text to COM1 (x64 only): ASCII as is, '?' for
   other code points (the port takes bytes; a code point's low byte would be
   garbage), and "\r\n" for a newline, as a serial terminal needs. */
static void SerialPutc(uint32_t c) {
#if defined(__x86_64__)
  auto put = [](uint8_t b) {
    while ((inb(0x3f8 + 5) & 0x20) == 0) {
    }
    outb(0x3f8, b);
  };
  if (c == '\n') {
    put('\r');
    put('\n');
  } else {
    put(c < 0x80 ? static_cast<uint8_t>(c) : '?');
  }
#else
  (void)c;
#endif
}

/* CHAR16 is uint16_t, which a C++ string literal does not convert to: the
   banners are u"..." (char16_t, the same representation). */
void EFIConOut(EFI_SYSTEM_TABLE* st, const char16_t* s) {
  if (st->ConOut)
    st->ConOut->OutputString(
        st->ConOut, reinterpret_cast<CHAR16*>(const_cast<char16_t*>(s)));
}

void EFIConOut(EFI_SYSTEM_TABLE* system_table, uint64_t v) {
  char16_t st[17];
  st[16] = 0;
  const CHAR16 hexdigits[] = {'0', '1', '2', '3', '4', '5', '6', '7',
                              '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};
  char16_t* nonzero = &st[15];  // always show at least a zero
  for (int i = 0; i < 16; ++i) {
    auto s = (v >> (4 * i)) & 0xF;
    if (s != 0) nonzero = st + (15 - i);
    st[15 - i] = hexdigits[s];
  }
  EFIConOut(system_table, nonzero);
}

void EFIConOut(EFI_SYSTEM_TABLE* system_table, const void* v) {
  EFIConOut(system_table, (uint64_t)v);
}

#ifdef KRAKEN_DEBUG
/* Debug builds (DEBUG=1 build.sh) spin here until a debugger clears the flag.
   The firmware picks the load address; runtime/efi/gdb/kraken.py finds it
   from the PC in this loop, loads the symbols there and clears the flag. */
extern "C" {
volatile UINT32 kraken_debug_wait = 1;
}

__attribute__((noinline)) void debug_wait() {
  while (kraken_debug_wait) cpu_relax();
}
#endif

uint32_t* video_base;
uint32_t video_hres;
uint32_t video_vres;
uint32_t video_stride;

uint32_t gCursorX = 0;
uint32_t gCursorY = 0;

/* The font tables of generate_font.cc, which build.sh makes from GNU Unifont
   and passes the paths of: the offsets file, then the bitmaps directly after
   it, read-only and 8-byte aligned. */
#if !defined(KRAKEN_FONT_OFFSETS) || !defined(KRAKEN_FONT_BITS)
#error "build with runtime/efi/build.sh: it defines the font tables' paths"
#endif
__asm__(
    ".section .rdata,\"dr\"\n"
    ".p2align 3\n"
    ".globl FontData\n"
    "FontData:\n"
    ".incbin \"" KRAKEN_FONT_OFFSETS
    "\"\n"
    ".incbin \"" KRAKEN_FONT_BITS
    "\"\n"
    ".text\n");
extern "C" const unsigned char FontData[];

struct GlyphBits {
  const unsigned char* bits; /* 16 bytes (8x16) or 32 (16x16), top row first */
  bool is_double;            /* 16x16 */
};

/* The glyph of code point c, or of '?' when the font has none for c. */
static GlyphBits GetBitsForCharacter(uint32_t c) {
  const uint64_t* header = reinterpret_cast<const uint64_t*>(&FontData);
  uint64_t pair_count = header[0];
  uint64_t max_char = header[1];
  /* Per run: its first code point, then the offset of its first glyph in bits
     (bit 31 set for a run of 16x16 glyphs). */
  const uint32_t* pairs = reinterpret_cast<const uint32_t*>(header + 2);
  const unsigned char* bits =
      reinterpret_cast<const unsigned char*>(pairs + 2 * pair_count);
  if (pair_count > 0 && c <= max_char && c >= pairs[0]) {
    /* The last run starting at or before c: pairs[l] <= c < pairs[h], with
       h == pair_count past the last run. */
    size_t l = 0, h = pair_count;
    while (h - l > 1) {
      size_t m = l + (h - l) / 2;
      if (pairs[2 * m] <= c) {
        l = m;
      } else {
        h = m;
      }
    }
    uint32_t first = pairs[2 * l];
    uint32_t offset = pairs[2 * l + 1] & 0x7FFFFFFF;
    bool is_double = (pairs[2 * l + 1] & 0x80000000) != 0;
    uint32_t size = is_double ? 32 : 16;
    /* The run's glyphs end where the next run's begin; the last run's at
       max_char. A code point past its run's end has no glyph. */
    uint64_t count = h < pair_count
                         ? ((pairs[2 * h + 1] & 0x7FFFFFFF) - offset) / size
                         : max_char - first + 1;
    if (c - first < count)
      return {bits + offset + (c - first) * size, is_double};
  }
  if (c == '?') return {nullptr, false}; /* no '?' in the font either */
  return GetBitsForCharacter('?');
}

uint32_t PlotCharacter(uint32_t ox, uint32_t oy, uint32_t c, uint32_t fg,
                       uint32_t bg) {
  if (oy + 16 > video_vres) return 0;
  auto [bp, wide] = GetBitsForCharacter(c);
  uint32_t width = wide ? 16 : 8;
  if (ox + width > video_hres) return 0;
  int bit = 0;
  for (uint32_t y = 0; y < 16; ++y) {
    for (uint32_t x = 0; x < width; ++x) {
      if (bit == 8) {
        ++bp;
        bit = 0;
      }
      video_base[video_stride * (oy + y) + ox + x] =
          (*bp & (1 << (7 - bit++))) ? fg : bg;
    }
  }
  return width;
}

EFI_STATUS InitVideo(EFI_SYSTEM_TABLE* system_table) {
  EFI_STATUS result;
  EFI_GUID gop_guid = EFI_GRAPHICS_OUTPUT_PROTOCOL_GUID;
  EFI_GRAPHICS_OUTPUT_PROTOCOL* gop;
  result = system_table->BootServices->LocateProtocol(&gop_guid, nullptr,
                                                      (void**)&gop);
  if (result != EFI_SUCCESS) {
    system_table->ConOut->OutputString(
        system_table->ConOut,
        (CHAR16*)L"Error finding graphics output protocol.\r\n");
    return result;
  }

  EFI_GRAPHICS_OUTPUT_MODE_INFORMATION* gop_info;
  UINTN gop_info_size, num_modes, native_mode;
  result = gop->QueryMode(gop, gop->Mode == nullptr ? 0 : gop->Mode->Mode,
                          &gop_info_size, &gop_info);
  if (result == EFI_NOT_STARTED) {
    result = gop->SetMode(gop, 0);
  }
  if (result != EFI_SUCCESS) {
    system_table->ConOut->OutputString(
        system_table->ConOut, (CHAR16*)L"Error finding graphics mode.\r\n");
    return result;
  }
  native_mode = gop->Mode->Mode;
  (void)native_mode;
  num_modes = gop->Mode->MaxMode;
  (void)num_modes;
  if (gop->Mode->Info->PixelFormat != PixelRedGreenBlueReserved8BitPerColor &&
      gop->Mode->Info->PixelFormat != PixelBlueGreenRedReserved8BitPerColor) {
    system_table->ConOut->OutputString(system_table->ConOut,
                                       (CHAR16*)L"Invalid pixel format.\r\n");
    return EFI_INVALID_PARAMETER;
  }
  bool video_rgb =
      gop->Mode->Info->PixelFormat == PixelRedGreenBlueReserved8BitPerColor;
  (void)video_rgb;
  video_base = (UINT32*)gop->Mode->FrameBufferBase;
  auto video_size = gop->Mode->FrameBufferSize;
  (void)video_size;
  video_hres = gop->Mode->Info->HorizontalResolution;
  video_vres = gop->Mode->Info->VerticalResolution;
  video_stride = gop->Mode->Info->PixelsPerScanLine;

  return EFI_SUCCESS;
}

void DisplayString(const char* st) {
  uint64_t n = 0;
  while (st[n]) ++n;
  DisplayChars(st, n);
}

void DisplayChars(const char* st, uint64_t n) {
  const char* end = st + n;
  while (st < end) {
    char c = st[0];
    SerialPutc(c);
    if (c == '\n') {
      gCursorX = 0;
      gCursorY += 16;
      if (gCursorY + 15 > video_vres) {
        gCursorY = 0;
      }
    } else {
      auto w = PlotCharacter(gCursorX, gCursorY, c, ~0, 0);
      if (w == 0) {
        gCursorX = 0;
        gCursorY += 16;
        if (gCursorY + 15 > video_vres) {
          gCursorY = 0;
        }
        continue;
      }
      gCursorX += w;
    }
    ++st;
  }
}

void DisplayUint64(uint64_t v) {
  char st[17];
  st[16] = 0;
  const char hexdigits[] = {'0', '1', '2', '3', '4', '5', '6', '7',
                            '8', '9', 'a', 'b', 'c', 'd', 'e', 'f'};
  char* nonzero = &st[15];  // always show at least a zero
  for (int i = 0; i < 16; ++i) {
    auto s = (v >> (4 * i)) & 0xF;
    if (s != 0) nonzero = st + (15 - i);
    st[15 - i] = hexdigits[s];
  }
  DisplayString(nonzero);
}

void Panic(const char* msg) {
  // First, so that no interrupt handler runs (and draws, or re-arms the
  // timer) while the message is written or afterwards.
  disable_interrupts();
  DisplayString("*** *** *** PANIC *** *** *** ");
  DisplayString(msg);
  for(;;) cpu_relax();
}

uint32_t kProcColors[8] = {0x810f19, 0x91111c, 0x801037, 0x570e75,
                           0x290cbc, 0x0c0be8, 0x0270fb, 0x2ad4f3};

extern uint32_t video_hres;  // sneaky

extern "C" void DebugSetIdleStatus() {
#if defined(__x86_64__)
  auto lapic_id = readgsqword(offsetof(Cpu, lapic_id));
  PlotCharacter(video_hres - 16 - 16 * lapic_id, 0, 0x1F63C,
                     kProcColors[lapic_id % 8], 0);
#endif
}

extern "C" void DebugSetActiveStatus() {
#if defined(__x86_64__)
  auto lapic_id = readgsqword(offsetof(Cpu, lapic_id));
  PlotCharacter(video_hres - 16 - 16 * lapic_id, 0, 0x1F63C,
                     0xFFFFFFFF, kProcColors[lapic_id % 8]);
#endif
}

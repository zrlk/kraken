// Converts a GNU Unifont .hex font (on standard input) into the stub's font
// tables, with the standard library only.
//
// Usage: generate_font OFFSETS_OUT BITS_OUT < unifont_all-17.0.05.hex
//   (runtime/efi/build.sh pipes in the gunzipped
//   runtime/efi/stub/unifont_all-17.0.05.hex.gz)
//
// Input: one glyph per line, "CODEPOINT:BITMAP" in hex, code points
// ascending; BITMAP is 32 hex digits (8x16 pixels, 16 bytes) or 64 (16x16,
// 32 bytes), one byte per two digits, rows top to bottom.
//
// Output, little-endian:
//   OFFSETS_OUT: uint64 run count, uint64 largest code point, then per run
//     uint32 first code point, uint32 offset into BITS_OUT of its first
//     glyph, with bit 31 set for a run of 16x16 glyphs.
//   BITS_OUT: the glyph bitmaps, back to back.
// A run is a maximal sequence of consecutive code points of the same width,
// so the glyph of code point c in the run starting at s is at
// offset + (c - s) * (16 or 32). make_binaries.cpp started runs only at a
// change of width; this also starts one after each gap in the code points
// (the file skips unassigned ranges), where that arithmetic would otherwise
// land on the wrong glyph. The format is the same.
#include <charconv>
#include <cstdint>
#include <cstdio>
#include <iostream>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

namespace {

bool ParseHex(std::string_view s, uint32_t* out) {
  if (s.empty()) return false;
  auto [end, ec] = std::from_chars(s.data(), s.data() + s.size(), *out, 16);
  return ec == std::errc() && end == s.data() + s.size();
}

bool WriteFile(const char* path, const void* data, size_t size) {
  FILE* f = fopen(path, "wb");
  if (!f) {
    perror(path);
    return false;
  }
  bool ok = fwrite(data, 1, size, f) == size;
  ok = fclose(f) == 0 && ok;
  if (!ok) perror(path);
  return ok;
}

}  // namespace

int main(int argc, char** argv) {
  if (argc != 3) {
    fprintf(stderr, "usage: %s OFFSETS_OUT BITS_OUT < font.hex\n", argv[0]);
    return 2;
  }
  int narrow = 0;
  int wide = 0;
  std::vector<std::pair<uint32_t, uint32_t>> offsets;
  std::vector<unsigned char> bits;
  size_t last_size = 0;
  uint64_t max_char = 0;
  bool first = true;
  std::string line;
  for (int line_no = 1; std::getline(std::cin, line); line_no++) {
    std::string_view next_line = line;
    if (!next_line.empty() && next_line.back() == '\r')
      next_line.remove_suffix(1);
    if (next_line.empty()) continue;
    auto delim = next_line.find(':');
    uint32_t char_val;
    if (delim == std::string_view::npos ||
        !ParseHex(next_line.substr(0, delim), &char_val)) {
      fprintf(stderr, "line %d: bad char code\n", line_no);
      return 1;
    }
    if (!first && char_val <= max_char) {
      fprintf(stderr, "line %d: code point %X not ascending\n", line_no,
              char_val);
      return 1;
    }
    next_line.remove_prefix(delim + 1);
    if (next_line.size() == 32) {
      narrow++;
    } else if (next_line.size() == 64) {
      wide++;
    } else {
      fprintf(stderr, "line %d: weird length: %zu\n", line_no,
              next_line.size());
      return 1;
    }
    if (first || next_line.size() != last_size || char_val != max_char + 1) {
      offsets.push_back(
          {char_val,
           static_cast<uint32_t>((next_line.size() == 64 ? 0x80000000 : 0) |
                                 bits.size())});
    }
    first = false;
    last_size = next_line.size();
    max_char = char_val;
    for (size_t b = 0; b < next_line.size(); b += 2) {
      uint32_t out;
      if (!ParseHex(next_line.substr(b, 2), &out)) {
        fprintf(stderr, "line %d: weird character data\n", line_no);
        return 1;
      }
      bits.push_back(static_cast<unsigned char>(out));
    }
  }
  if (first) {
    fprintf(stderr, "no glyphs on standard input\n");
    return 1;
  }
  if (bits.size() >= 0x80000000) {
    fprintf(stderr, "font too large: %zu bytes of bitmaps\n", bits.size());
    return 1;
  }
  fprintf(stderr, "%d single-width, %d chonks, %zu runs, %zu bytes\n", narrow,
          wide, offsets.size(), bits.size());

  std::vector<unsigned char> table;
  auto put = [&table](uint64_t v, int n) {
    for (int i = 0; i < n; i++)
      table.push_back(static_cast<unsigned char>(v >> (8 * i)));
  };
  put(offsets.size(), 8);
  put(max_char, 8);
  for (const auto& [code, offset] : offsets) {
    put(code, 4);
    put(offset, 4);
  }
  return WriteFile(argv[1], table.data(), table.size()) &&
                 WriteFile(argv[2], bits.data(), bits.size())
             ? 0
             : 1;
}

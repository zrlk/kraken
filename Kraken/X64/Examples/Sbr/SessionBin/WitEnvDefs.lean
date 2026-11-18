import Kraken.X64.Examples.Sbr.Linked
import Kraken.X64.Examples.Sbr.Parse.GridJtWit
import Kraken.X64.Examples.Sbr.SessionSpec

/-!
# The witness environment: the image, the ambient code, the setup

The fixed parameters under which the hypotheses of the five theorems of `SessionBin/Api.lean`
are shown to hold together:

* the stand-in texts of the external routines (their contracts: `WitLeaf*.lean`);
* the image `img`: every text of `SessPlaced`, the stand-ins, one cell per read-only constant
  the specifications name, laid out by `wLayout` (labels take no bytes, every other cell 8192,
  from `0x400000`); the ambient code `wCE`;
* the caller's environment `wEnv`, the setup `wS`, and init's state `wX` (a bump allocator's
  heap).

Data addresses: the constants sit at their labels (below `2 ^ 32`); the Huffman tables at
`wSbrTab k`, `wPsTab k`; the transform tables, the PS tables and the logging state are 64-byte
blocks at `0x300200000`, `0x300201000`, `0x300202000`; the heap pointer at `wHeapPtr`, the heap
`[wHeapStart, wHeapEnd)`.
-/

open Kraken Kraken.X64.Parser Kraken.SysV Mem
open Kraken.Examples.Sbr.Apply (Env Fns)

namespace Kraken.Examples.Sbr.WitEnv

/-! ## Addresses -/

/-- The cell holding the allocator's next free address. -/
abbrev wHeapPtr : BitVec 64 := 0x400000000#64

/-- The heap's first byte (32-aligned). -/
abbrev wHeapStart : BitVec 64 := 0x400001000#64

/-- The heap's end (32-aligned): 1 MiB, room for init's 0x88ba0-byte element. -/
abbrev wHeapEnd : BitVec 64 := 0x400101000#64

/-- FFmpeg's SBR Huffman table `k`. -/
def wSbrTab (k : Nat) : BitVec 64 := 0x300000000#64 + BitVec.ofNat 64 (0x2000 * k)

/-- FFmpeg's PS Huffman table `k`. -/
def wPsTab (k : Nat) : BitVec 64 := 0x300100000#64 + BitVec.ofNat 64 (0x2000 * k)

/-- The `av_tx` tables. -/
abbrev wTxTabA : BitVec 64 := 0x300200000#64

/-- The PS decoder's tables. -/
abbrev wPsTabA : BitVec 64 := 0x300201000#64

/-- The logging state. -/
abbrev wExtA : BitVec 64 := 0x300202000#64

/-- The external routines' stack. -/
abbrev wK : Nat := 0x100

/-! ## The stand-ins -/

/-- `av_log`: return at once. -/
def avLogT : Program := parse("
av_log:
    ret
")

/-- `avpriv_request_sample`: return at once. -/
def avReqT : Program := parse("
avpriv_request_sample:
    ret
")

/-- `ff_psdsp_init`: return at once (writes nothing). -/
def psdspT : Program := parse("
ff_psdsp_init:
    ret
")

/-- `ff_ps_apply`: return at once. -/
def psApplyT : Program := parse("
ff_ps_apply:
    ret
")

/-- The transform `av_tx_init` hands out: return at once. -/
def txFnT : Program := parse("
tx_stub:
    ret
")

/-- `powf`: `1.0f`. -/
def powfT : Program := parse("
powf:
    mov $0x3f800000,%eax
    vmovd %eax,%xmm0
    ret
")

/-- `log2f`: `1.0f`. -/
def log2fT : Program := parse("
log2f:
    mov $0x3f800000,%eax
    vmovd %eax,%xmm0
    ret
")

/-- `av_tx_init`: `*tx = tx_stub`, `*ctx = 0`, result `0`. -/
def txInitT : Program := parse("
av_tx_init:
    lea tx_stub(%rip),%rax
    mov %rax,(%rsi)
av_tx_init.ctx:
    xor %eax,%eax
    mov %rax,(%rdi)
av_tx_init.done:
    ret
")

/-- `av_mallocz(n)`: a bump allocator. The next free address `p` (32-aligned) is in the cell
`wHeapPtr`; if `n ≤ wHeapEnd - p` it returns `p`, moves the pointer to `p + n` rounded up to
32, and zeroes `n` bytes at `p`; otherwise it returns `NULL`. -/
def malloczT : Program := parse("
av_mallocz:
    movabs $0x400000000,%r8
    mov (%r8),%rax
    movabs $0x400101000,%rcx
    sub %rax,%rcx
    cmp %rcx,%rdi
    ja av_mallocz.fail
av_mallocz.bump:
    lea 0x1f(%rdi),%rdx
    and $0xffffffffffffffe0,%rdx
    add %rax,%rdx
    mov %rdx,(%r8)
    xor %ecx,%ecx
    test %rdi,%rdi
    je av_mallocz.done
av_mallocz.loop:
    xor %edx,%edx
    mov %dl,(%rax,%rcx,1)
    inc %rcx
    cmp %rdi,%rcx
    jb av_mallocz.loop
av_mallocz.done:
    ret
av_mallocz.fail:
    xor %eax,%eax
    ret
")

/-- `memcpy(dst, src, n)`: a byte loop. -/
def memcpyT : Program := parse("
memcpy:
    xor %ecx,%ecx
    test %rdx,%rdx
    je memcpy.done
memcpy.loop:
    movzbl (%rsi,%rcx,1),%eax
    mov %al,(%rdi,%rcx,1)
    inc %rcx
    cmp %rdx,%rcx
    jb memcpy.loop
memcpy.done:
    ret
")

/-- `memset(dst, c, n)`: a byte loop; returns `dst`. -/
def memsetT : Program := parse("
memset:
    mov %rdi,%rax
    xor %ecx,%ecx
    test %rdx,%rdx
    je memset.done
memset.loop:
    mov %sil,(%rdi,%rcx,1)
    inc %rcx
    cmp %rdx,%rcx
    jb memset.loop
memset.done:
    ret
")

/-- `ff_sbrdsp_init(s)`: the fourteen `sbr->dsp` slots as `ff_sbrdsp_init_x86` sets them with
SSE, SSE2 and SSE3 (`autocorrelate`: the SSE version), two per block. -/
def sbrdspT : Program := parse("
ff_sbrdsp_init:
    lea ff_sbr_sum64x5_sse(%rip),%rax
    mov %rax,(%rdi)
    lea ff_sbr_sum_square_sse(%rip),%rax
    mov %rax,0x8(%rdi)
ff_sbrdsp_init.s2:
    lea ff_sbr_neg_odd_64_sse(%rip),%rax
    mov %rax,0x10(%rdi)
    lea ff_sbr_qmf_pre_shuffle_sse2(%rip),%rax
    mov %rax,0x18(%rdi)
ff_sbrdsp_init.s4:
    lea ff_sbr_qmf_post_shuffle_sse(%rip),%rax
    mov %rax,0x20(%rdi)
    lea ff_sbr_qmf_deint_neg_sse(%rip),%rax
    mov %rax,0x28(%rdi)
ff_sbrdsp_init.s6:
    lea ff_sbr_qmf_deint_bfly_sse2(%rip),%rax
    mov %rax,0x30(%rdi)
    lea ff_sbr_autocorrelate_sse(%rip),%rax
    mov %rax,0x38(%rdi)
ff_sbrdsp_init.s8:
    lea ff_sbr_hf_gen_sse(%rip),%rax
    mov %rax,0x40(%rdi)
    lea ff_sbr_hf_g_filt_sse(%rip),%rax
    mov %rax,0x48(%rdi)
ff_sbrdsp_init.s10:
    lea ff_sbr_hf_apply_noise_0_sse2(%rip),%rax
    mov %rax,0x50(%rdi)
    lea ff_sbr_hf_apply_noise_1_sse2(%rip),%rax
    mov %rax,0x58(%rdi)
ff_sbrdsp_init.s12:
    lea ff_sbr_hf_apply_noise_2_sse2(%rip),%rax
    mov %rax,0x60(%rdi)
    lea ff_sbr_hf_apply_noise_3_sse2(%rip),%rax
    mov %rax,0x68(%rdi)
ff_sbrdsp_init.done:
    ret
")

/-! ## The image -/

/-- The read-only constants the specifications name (`CstW`, `PStat`). -/
def dataLabels : List Label :=
  Linked.dataLabels ++
  ["read_sbr_grid_jt", "ceil_log2", "ff_aac_sbr_vlc", "vlc_ps", "num_env_tab",
   "nr_iidicc_par_tab", "nr_iidopd_par_tab", "huff_iid", "ff_log2_tab_got", "ff_log2_tab",
   "LCPI0_28", "LCPI0_30", "sbr_offset_0", "sbr_offset_1", "sbr_offset_2", "sbr_offset_3",
   "sbr_offset_4", "sbr_offset_5", "LCPI5_0", "LCPI5_1", "LCPI5_2", "LCPI5_3", "LCPI5_4",
   "LCPI5_6", "LCPI5_8", "LCPI5_9", "sbr_make_f_tablelim_bw"]

/-- One data cell per constant, at its label. -/
def dataT : List Program := dataLabels.map fun l => [.label l, .byteArray ByteArray.empty]

/-- The parser's and init's texts. -/
def parserT : List Program :=
  [Grid.body, DecExt.body, Usac.body, Usac.cbody, Hdr.body, Reset.body, Tlim.body, Dtdf.body,
   Invf.body, Env.body, Noise.body, Ps.body, Init.body]

/-- The stand-ins of the external routines. -/
def standT : List Program :=
  [avLogT, avReqT, psdspT, psApplyT, txFnT, powfT, log2fT, txInitT, malloczT, memcpyT, memsetT,
   sbrdspT]

/-- All texts but `ff_aac_sbr_apply`. -/
def otherT : List Program := dataT ++ parserT ++ Linked.codeT ++ standT

/-- All texts; `ff_aac_sbr_apply` last. -/
def texts : List Program := otherT ++ [Kraken.Examples.Sbr.Apply.body]

/-- The image. -/
def img : Program := texts.flatten

/-! ## The layout -/

/-- `layOf p` is a valid layout of `p` when no cell is an `.align` and `p` is not huge. -/
theorem layOf_valid (p : Program) (hA : p.all Linked.noAlign = true) (hL : p.length < 2 ^ 40) :
    Executable.ValidLayout (GridJtWit.layOf p p) where
  label_size i l z h := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, rfl, rfl⟩ := h
    show (if (p[i]?.map Directive.isLabel).getD false then 0 else 8192) = 0
    simp [hd, Directive.isLabel]
  instr_size i d z h hnl := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d', hd, rfl, rfl⟩ := h
    have : d'.isLabel = false := by
      cases d' <;> simp_all [Directive.isLabel]
    show 0 < (if (p[i]?.map Directive.isLabel).getD false then 0 else 8192)
    simp [hd, this]
  no_wrap := by
    have hle : ∀ x ∈ (GridJtWit.layOf p p).2, x.2 ≤ 8192 := by
      intro x hx
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hx
      simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff] at hi
      obtain ⟨d, -, rfl⟩ := hi
      show (if (p[i]?.map Directive.isLabel).getD false then 0 else 8192) ≤ 8192
      split <;> omega
    have h := Linked.sum_snd_le _ 8192 hle
    have hlen : (GridJtWit.layOf p p).2.length = p.length := by simp [Kraken.Layout.apply]
    omega
  align_addr i aw w n pad z h hn := by
    simp only [Kraken.Layout.apply, List.getElem?_mapIdx, Option.map_eq_some_iff,
      Prod.mk.injEq] at h
    obtain ⟨d, hd, hdeq, -⟩ := h
    subst hdeq
    have := List.all_eq_true.mp hA _ (List.mem_of_getElem? hd)
    simp [Linked.noAlign] at this

theorem img_noAlign : img.all Linked.noAlign = true := by decide +kernel

theorem img_length : img.length < 2 ^ 40 := by decide +kernel

/-- The image's layout. -/
@[reducible] def wLayout : _root_.Layout := GridJtWit.layOf img

instance wLayout_valid : @Executable.ValidLayout (wLayout img) :=
  layOf_valid img img_noAlign img_length

/-- **The ambient code**: the laid-out image. -/
@[instance_reducible] def wCE : CodeEnv := ⟨@wLayout img⟩

/-! ## The environment and the setup -/

section
attribute [local instance] wCE

/-- The function slots: `SbrSlots`' routines; both transforms are `tx_stub`. -/
def wFns : Fns where
  sum64x5 := entry "ff_sbr_sum64x5_sse"
  sumSquare := entry "ff_sbr_sum_square_sse"
  preShuffle := entry "ff_sbr_qmf_pre_shuffle_sse2"
  postShuffle := entry "ff_sbr_qmf_post_shuffle_sse"
  autocorr := entry "ff_sbr_autocorrelate_sse"
  hfGen := entry "ff_sbr_hf_gen_sse"
  hfs := { gfilt := entry "ff_sbr_hf_g_filt_sse", noise0 := entry "ff_sbr_hf_apply_noise_0_sse2",
           noise1 := entry "ff_sbr_hf_apply_noise_1_sse2",
           noise2 := entry "ff_sbr_hf_apply_noise_2_sse2",
           noise3 := entry "ff_sbr_hf_apply_noise_3_sse2" }
  qfs := { negOdd64 := entry "ff_sbr_neg_odd_64_sse", deintNeg := entry "ff_sbr_qmf_deint_neg_sse",
           deintBfly := entry "ff_sbr_qmf_deint_bfly_sse2", tx := entry "tx_stub",
           fmul := entry "ff_vector_fmul_sse", fmulAdd := entry "ff_vector_fmul_add_sse" }
  lfGen := entry "sbr_lf_gen"
  hfAsm := entry "sbr_hf_assemble"
  xGen := entry "sbr_x_gen"
  hfInv := entry "sbr_hf_inverse_filter"
  mdctAna := entry "tx_stub"
  fmulRev := entry "ff_vector_fmul_reverse_sse"

/-- **The caller's environment** (also the element's): the transform contexts own nothing
(`tx_stub` reads nothing), the `av_tx` tables, the PS tables and the logging state are 64-byte
blocks. -/
def wEnv : Env where
  fs := wFns
  Ctx _ := Std.ExtHashMap.emp
  TxTab := 64 ?@ wTxTabA
  PsTab := 64 ?@ wPsTabA
  Ext := 64 ?@ wExtA

/-- **The setup**: stack `wK` for each external routine, `powf`/`log2f` the constant `1.0f`
(`Reset.bandsOK_const`), FFmpeg's Huffman tables at `wSbrTab`, `wPsTab`. -/
def wS : SessionBin.Setup where
  k := wK
  env := wEnv
  pw _ _ := Reset.f1
  lg _ := Reset.f1
  sbrTabs := wSbrTab
  psTabs := wPsTab

/-- **Init's state**: the allocator's heap. The cell `wHeapPtr` holds the next free address `p`
(32-aligned, at most `wHeapEnd`), the bytes `[p, wHeapEnd)` are free, and any further bytes
(the rounding gaps of earlier allocations) belong to the allocator too. Before the first
allocation, `p = wHeapStart` and there are no further bytes. -/
def wX : Mem 64 → Prop := fun m => ∃ p : BitVec 64,
  isAligned 32 p = true ∧ p.toNat ≤ wHeapEnd.toNat
  ∧ (Apply.c8 wHeapPtr p ⋆ ((wHeapEnd - p).toNat ?@ p ⋆ fun _ => True)) m

end

end Kraken.Examples.Sbr.WitEnv

/-
**hello.w's `wc_rodata` from the allocator's return, and `scc_rt_main`'s `.x2` block, at `ownGHXW`** (x86-64
only; the `ownGHXW` instance of `Spike/Lib/X64HelloRdPostWI.lean`, as `X64HelloRdPreWIX` is `X64HelloRdPreWI`'s):
`WcW.rdPostW_wcGH` and `mB1W_wcGH` (inside `SFactsSt2` at `ownGH`) moved to `SFactsSt2` at `ownGHXW` (`Lft2H`),
node for node (`BlkW.imp`, `NodeW.imp`). `.x15`'s pcs, `scc_rt_main`'s `.x2` and the blocks' ends (`.x2`,
`wc_main`) are `QPH` pcs (off the take site: `PPH`), and the frames are on the pool (`hb`, `hbM`), so every state
holds `tcbM` only (`cls_poolH`). The exchanges' loads write nothing, their stores write the buffer, off `tcbM`
(`hbufM`).

- `rp_labsH`: the labels the pcs are decided from.
- `hw_ldH`: a plain load writes nothing.
- `ldLH`, `stLH`: a load / store `k(%rcx)` at `.x15 + o` inside `Lft2H`.
- `rdPostLH`, `mB1LH`: `RdPostW` and `.x2`'s block inside `Lft2H`.
- `rdPostW_wcGHX`, `mB1W_wcGHX`: the producers at `ownGHXW`.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (`A64HelloRdPostWI` at `ownGH` is the whole chain).
Against `X64HelloRdPreWIX`: there is no allocator call, so no `hnoM`; the buffer's stores need their words off
`tcbM` (`hbufM`, as `X64HelloOwnWcPreX`'s box store's `hboxM`); `scc_rt_main`'s `.x2` block runs in
`scc_rt_main`'s region, its band `[-288, 8]` (`hbM`; `Hello1.mB1_ok`'s bounds).
-/
import Spike.Lib.X64HelloRdPostWI
import Spike.Lib.X64HelloRdPreWIX

namespace Spike.Lib.X64.HelloPh.OwnRd

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq code_field blockAtB)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At ldDir stDir mB bAddr arun)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.Flow.HelloRd (pN RdPostW rpIn hello_rpIn)
open Spike.Lib.X64.Flow.Hello1 (rpB0 rpB0_ok rpB0_run rpB1 rpB1_ok rpB1_run rpB2 rpB2_ok rpB2_run rpB3
  rpB3_ok rpB3_run rpB4 rpB4_ok rpB4_run bAddr_rcx_rax mB1 mB1_ok mB1_run mS0)
open Spike.Lib.X64.WakePh (tcbM BandOnP keep_pc)
open Spike.Lib.X64.WakePh.Tcb2W (soRun)
open Spike.Lib.X64.WakePh.StartTi (keep_ld keep_st)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Kraken.Promising.Lower.X64 (CellAt eaddr)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop} {rS : Range}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- The labels `.x15`'s and `.x2`'s pcs are decided from, at the canonical base. -/
theorem rp_labsH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab ".Lwc_rodata.x15" = Int64.ofNat 4203184 ∧ L.lab ".Lscc_rt_main.x2" = Int64.ofNat 4198576 ∧
    L.lab "wc_main" = Int64.ofNat 4203623 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- **A load `movq i(%b), %r`** of an unmapped word writes nothing. -/
theorem hw_ldH {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)} {b r : Reg64}
    {i : Int64} {z : Nat} {A : BitVec 64}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (ldDir b i r) z ∧ eaddr s z (mB b i) = A ∧
      Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {}) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_load_agrees hc ha hd (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  exact fun _ => trivial

/-- `wc_rodata`'s and `scc_rt_main`'s offsets (`oR`, `mO` alone are ambiguous here). -/
local notation "oR1" => Spike.Lib.X64.Flow.Hello1.oR

/-- See `oR1`. -/
local notation "mO1" => Spike.Lib.X64.Flow.Hello1.mO

/-- `hso` of a block of `wc_rodata` at offsets `o`, decided. -/
local macro "soRPH " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -208 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

/-- `hso` of a block of `scc_rt_main` at offsets `o`, decided. -/
local macro "soMPH " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -288 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

omit hsite in
/-- **A load `movq k(%rcx), %rax` at `.x15 + o` inside `Lft2H`**: its word unmapped under `F` (`hun`), its pc
and next pc `QPH` (`hpc`). -/
theorem ldLH (hb : BandOnP L R (-208) 8) {n : ND} {k : Int64} {o z : Nat}
    (hbl : blockAtB helloCells ".Lwc_rodata.x15" o [(ldDir .rcx k .rax, z)] = true)
    (he : L.lab ".Lwc_rodata.x15" + Int64.ofNat o = n.pc)
    (hpc : QPH n.pc.toBitVec.toNat ∧ QPH (n.pc + Int64.ofNat z).toBitVec.toNat)
    (hso : -208 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hun : ∀ σ c, n.J σ c → ∀ m, F m → Mem.loadInt m.dmem (bAddr σ.regs .rcx k) 8 = none) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n := by
  refine Spike.Lib.X64.WakePh.WcW.NodeW.ofAll (fun σ => bAddr σ.regs .rcx k) fun A => ?_
  by_cases hA : ∀ m, F m → Mem.loadInt m.dmem A 8 = none
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd (hun σ c hJ) hA
  have hE : ∀ s c, At L.exe L.endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ bAddr σ.regs .rcx k = A⟩ s c →
      CellAt s (ldDir .rcx k .rax) z ∧ eaddr s z (mB .rcx k) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧
        s.decls = {} := by
    rintro s c ⟨he', hn, hd, hp', σ, hA', hF, hJ, hsA⟩
    exact ⟨(code_field L.lays rfl (hp ▸ hbl) he s he' hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s z .rcx k).trans (by rw [hA'.regs]; exact hsA), hA _ hF, hd⟩
  refine nodeL2H hsep ha hW (sz := z) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) hpc hso
    (hw_ldH hE)
  obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
  have hK := keep_ld (by decide) hc hd hea hun' hs
  exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩

omit hsite in
/-- **A store `movq %rax, k(%rcx)` at `.x15 + o` inside `Lft2H`** (as `ldLH`): its word also off `tcbM`
(`hM`). -/
theorem stLH (hb : BandOnP L R (-208) 8) {n : ND} {k : Int64} {o z : Nat}
    (hbl : blockAtB helloCells ".Lwc_rodata.x15" o [(stDir .rcx k .rax, z)] = true)
    (he : L.lab ".Lwc_rodata.x15" + Int64.ofNat o = n.pc)
    (hpc : QPH n.pc.toBitVec.toNat ∧ QPH (n.pc + Int64.ofNat z).toBitVec.toNat)
    (hso : -208 ≤ n.o.sp ∧ n.o.sp ≤ 8)
    (hun : ∀ σ c, n.J σ c → ∀ m, F m → Mem.loadInt m.dmem (bAddr σ.regs .rcx k) 8 = none)
    (hM : ∀ σ c, n.J σ c → bAddr σ.regs .rcx k ≠ tcbM L) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n := by
  refine Spike.Lib.X64.WakePh.WcW.NodeW.ofAll (fun σ => bAddr σ.regs .rcx k) fun A => ?_
  by_cases hA : (∀ m, F m → Mem.loadInt m.dmem A 8 = none) ∧ A ≠ tcbM L
  case neg =>
    rintro s c ⟨-, -, -, -, σ, -, -, hJ, rfl⟩
    exact absurd ⟨hun σ c hJ, hM σ c hJ⟩ hA
  have hE : ∀ s c, At L.exe L.endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ bAddr σ.regs .rcx k = A⟩ s c →
      CellAt s (stDir .rcx k .rax) z ∧ eaddr s z (mB .rcx k) = A ∧ Mem.loadInt s.st.1.dmem A 8 = none ∧
        s.decls = {} := by
    rintro s c ⟨he', hn, hd, hp', σ, hA', hF, hJ, hsA⟩
    exact ⟨(code_field L.lays rfl (hp ▸ hbl) he s he' hn).cell0 rfl rfl hp',
      (Spike.Lib.X64.eaddr_mB s z .rcx k).trans (by rw [hA'.regs]; exact hsA), hA.1 _ hF, hd⟩
  refine nodeL2H hsep ha hW (sz := z) (P := QPH) (cls_poolH hlab hb) (fun s c hAt s' hs => ?_) hpc hso
    (Spike.Lib.X64.WakePh.OwnSt.hw_stM hE hA.2)
  obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
  have hK := keep_st hc hd hea hun' hs
  exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩

set_option maxHeartbeats 1600000 in
/-- **`RdPostW` inside `Lft2H`**: the buffer's two words unmapped under `F` (`hun`) and off `tcbM` (`hM`) at
every `.x15` state, the return address at the stack top `scc_rt_main`'s `.x2` (`hra`). -/
theorem rdPostLH (hb : BandOnP L R (-208) 8) (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hun : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) →
      ∀ m, F m → Mem.loadInt m.dmem (bAddr σ0.regs .rax i) 8 = none)
    (hM : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → bAddr σ0.regs .rax i ≠ tcbM L)
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot 0 = (L.lab ".Lscc_rt_main.x2").toBitVec) :
    RdPostW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  obtain ⟨eX, eM, -⟩ := rp_labsH hlab (L := L)
  have hin := hello_rpIn
  simp only [rpIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨b0, bl1⟩, b1⟩, bx1⟩, b2⟩, bl2⟩, b3⟩, bx2⟩, b4⟩ := hin
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) b0 (ofNat_zero' _) rpB0_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRPH rpB0 oR1)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab ".Lwc_rodata.x15" + _).toBitVec.toNat; rw [eX]; revert k; decide +kernel
    · show QPH (arun L.lab rpB0 ⟨L.lab ".Lwc_rodata.x15", oR1, σ⟩).pc.toBitVec.toNat
      rw [rpB0_run, eX]; dsimp only; decide +kernel
  · exact ldLH hp hlab hsep ha hW hb (o := 8) bl1 rfl
      (by show QPH (L.lab ".Lwc_rodata.x15" + 8).toBitVec.toNat ∧
            QPH (L.lab ".Lwc_rodata.x15" + 8 + Int64.ofNat 3).toBitVec.toNat
          rw [eX]; decide +kernel)
      (by dsimp only [pN]; decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hun σ0 c0 hJp 0 (.inl rfl)
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (k := 11) b1 rfl rpB1_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRPH rpB1 oR1)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab ".Lwc_rodata.x15" + 11 + _).toBitVec.toNat; rw [eX]; revert k; decide +kernel
    · show QPH (arun L.lab rpB1 ⟨L.lab ".Lwc_rodata.x15" + 11, oR1, σ⟩).pc.toBitVec.toNat
      rw [rpB1_run, eX]; dsimp only; decide +kernel
  · exact stLH hp hlab hsep ha hW hb (o := 29) bx1 rfl
      (by show QPH (L.lab ".Lwc_rodata.x15" + 29).toBitVec.toNat ∧
            QPH (L.lab ".Lwc_rodata.x15" + 29 + Int64.ofNat 3).toBitVec.toNat
          rw [eX]; decide +kernel)
      (by dsimp only [pN]; decide)
      (fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hun σ0 c0 hJp 0 (.inl rfl))
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hM σ0 c0 hJp 0 (.inl rfl)
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (k := 32) b2 rfl rpB2_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRPH rpB2 oR1)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab ".Lwc_rodata.x15" + 32 + _).toBitVec.toNat; rw [eX]; revert k; decide +kernel
    · show QPH (arun L.lab rpB2 ⟨L.lab ".Lwc_rodata.x15" + 32, oR1, σ⟩).pc.toBitVec.toNat
      rw [rpB2_run, eX]; dsimp only; decide +kernel
  · exact ldLH hp hlab hsep ha hW hb (o := 36) bl2 rfl
      (by show QPH (L.lab ".Lwc_rodata.x15" + 36).toBitVec.toNat ∧
            QPH (L.lab ".Lwc_rodata.x15" + 36 + Int64.ofNat 4).toBitVec.toNat
          rw [eX]; decide +kernel)
      (by dsimp only [pN]; decide)
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hun σ0 c0 hJp 8 (.inr rfl)
  · refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (k := 40) b3 rfl rpB3_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRPH rpB3 oR1)
      (fun σ c _ => ?_)
    · intro k hk; show PPH (L.lab ".Lwc_rodata.x15" + 40 + _).toBitVec.toNat; rw [eX]; revert k; decide +kernel
    · show QPH (arun L.lab rpB3 ⟨L.lab ".Lwc_rodata.x15" + 40, oR1, σ⟩).pc.toBitVec.toNat
      rw [rpB3_run, eX]; dsimp only; decide +kernel
  · exact stLH hp hlab hsep ha hW hb (o := 58) bx2 rfl
      (by show QPH (L.lab ".Lwc_rodata.x15" + 58).toBitVec.toNat ∧
            QPH (L.lab ".Lwc_rodata.x15" + 58 + Int64.ofNat 4).toBitVec.toNat
          rw [eX]; decide +kernel)
      (by dsimp only [pN]; decide)
      (fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hun σ0 c0 hJp 8 (.inr rfl))
      fun σ c ⟨σ0, ⟨c0, hJp⟩, _, _, _, hx⟩ => by rw [bAddr_rcx_rax hx]; exact hM σ0 c0 hJp 8 (.inr rfl)
  · have hend : ∀ σ c, (pN L.lab Jp Jp' J1 J2 J2' J3 J4 .s4).J σ c →
        (arun L.lab rpB4 ⟨L.lab ".Lwc_rodata.x15" + 62, oR1, σ⟩).pc = L.lab ".Lscc_rt_main.x2" := by
      rintro σ c ⟨σ0, ⟨c0, hJp⟩, -, hfr⟩
      rw [rpB4_run, hfr.2.2.1, hra σ0 c0 hJp, Int64.ofBitVec_toBitVec]
    refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) (k := 62) b4 rfl rpB4_ok hR hRlo hhi
      (fun _ h => h.2) (fun s h => cls_poolH hlab hb s h.1) (cls_poolH hlab hb) ?_ (soRPH rpB4 oR1)
      (fun σ c hJ => ?_)
    · intro k hk; show PPH (L.lab ".Lwc_rodata.x15" + 62 + _).toBitVec.toNat; rw [eX]; revert k; decide +kernel
    · show QPH (arun L.lab rpB4 ⟨L.lab ".Lwc_rodata.x15" + 62, oR1, σ⟩).pc.toBitVec.toNat
      rw [hend σ c hJ, eM]; decide +kernel

/-- **`scc_rt_main`'s `.x2` block inside `Lft2H`** (the call of `wc_main`), its band `[-288, 8]` on the pool
(`hbM`). -/
theorem mB1LH (hbM : BandOnP L R (-288) 8) (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {σC : Spike.Lib.X64.AS} {Jr : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1 := by
  obtain ⟨-, eM, eW⟩ := rp_labsH hlab (L := L)
  have hin := Spike.Lib.X64.Flow.HelloM.hello_mainIn
  simp only [Spike.Lib.X64.Flow.Hello1.mainIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨-, b1⟩, -⟩, -⟩ := hin
  refine blkL2H hp hlab hsite hsep ha hW (P := PPH) (Q := QPH) b1 (ofNat_zero' _) mB1_ok hR hRlo hhi
    (fun _ h => h.2) (fun s h => cls_poolH hlab hbM s h.1) (cls_poolH hlab hbM) ?_ (soMPH mB1 mO1)
    (fun σ c _ => ?_)
  · intro k hk; show PPH (L.lab ".Lscc_rt_main.x2" + _).toBitVec.toNat; rw [eM]; revert k; decide +kernel
  · show QPH (arun L.lab mB1 ⟨L.lab ".Lscc_rt_main.x2", mO1, σ⟩).pc.toBitVec.toNat
    rw [mB1_run, eW]; dsimp only; decide +kernel

end L

/-! ## The producers at `ownGHXW` -/

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
  (hsep : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlo hΛ hlab hsite hsep ha hW

/-- **`WcW.rdPostW_wcGH` at `ownGHXW`** (owned word `a`): `rdPostW_wcGH`'s premises, `ownGHXW`'s separation
(`hsep`, `ha`, `hW`), `wc_rodata`'s band `[-208, 8]` on the pool (`hb`, `rdPreW_wcGHX`'s), and the buffer's two
words off `tcbM` (`hbufM`). -/
theorem rdPostW_wcGHX (hb : BandOnP L R (-208) 8) (hR : R.OK) (hRlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    {Jp Jp' J1 J2 J2' J3 J4 : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop}
    (hbuf : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → WcW.BoxOkH Λ L a F (bAddr σ0.regs .rax i))
    (hbufM : ∀ σ0 c, Jp σ0 c → ∀ i : Int64, (i = 0 ∨ i = 8) → bAddr σ0.regs .rax i ≠ tcbM L)
    (hra : ∀ σ0 c, Jp σ0 c → σ0.slot 0 = (L.lab ".Lscc_rt_main.x2").toBitVec) :
    RdPostW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F Jp Jp' J1 J2 J2' J3 J4 := by
  have h := WcW.rdPostW_wcGH hp hlo hΛ hlab hsite a (rS := rS) (Jp' := Jp') (J1 := J1) (J2 := J2) (J2' := J2')
    (J3 := J3) (J4 := J4) hR hRlo hhi hbuf hra
  have l := rdPostLH (Λ := Λ) (Dt := fun _ => False) (Jp' := Jp') (J1 := J1) (J2 := J2) (J2' := J2')
    (J3 := J3) (J4 := J4) hp hlab hsite hsep ha hW hb hR hRlo hhi
    (fun σ0 c hJ i hi => (hbuf σ0 c hJ i hi).2.1) hbufM hra
  exact ⟨Spike.Lib.X64.AllocG.BlkW.imp h.s0 l.s0 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.l1 l.l1 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.s1 l.s1 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.x1 l.x1 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.s2 l.s2 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.l2 l.l2 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.s3 l.s3 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.NodeW.imp h.x2 l.x2 fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.s4 l.s4 fun _ _ h1 h2 => h2 h1⟩

/-- **`WcW.mB1W_wcGH` at `ownGHXW`**: `scc_rt_main`'s band `[-288, 8]` on the pool (`hbM`). -/
theorem mB1W_wcGHX (hbM : BandOnP L R (-288) 8) (hR : R.OK) (hRlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {σC : Spike.Lib.X64.AS} {Jr : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s) (Spike.Lib.X64.PhRec.K L rS)
      L.exe L.endPc R F (mS0 L.lab R σC Jr) mB1 :=
  Spike.Lib.X64.AllocG.BlkW.imp (WcW.mB1W_wcGH hp hlo hΛ hlab hsite a hR hRlo hhi)
    (mB1LH (Λ := Λ) (Dt := fun _ => False) hp hlab hsite hsep ha hW hbM hR hRlo hhi) fun _ _ h1 h2 => h2 h1

end Inst

end Spike.Lib.X64.HelloPh.OwnRd

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.rdPostLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.rdPostLH

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.mB1LH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.mB1LH

/--
info: 'Spike.Lib.X64.HelloPh.OwnRd.rdPostW_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.rdPostW_wcGHX

/-- info: 'Spike.Lib.X64.HelloPh.OwnRd.mB1W_wcGHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.OwnRd.mB1W_wcGHX

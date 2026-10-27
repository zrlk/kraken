/-
**`wc_rodata`'s allocation continuation on x64**: a fresh label's landing
in the allocator is at `wc_rodata`'s `.x13` for any placement of the label
at the landing's base, and from there the rest of `wc_rodata` runs to the
setup block's return (`Spike/Lib/X64Hello1RodataSetup.lean`), the `%fs`
base kept. The x64 twin of `Spike/Lib/A64Hello1RodataXa.lean`.

- `aR_off_neg8`, `aR_off_0`: the frame record's cells lie outside the
  allocator's region;
- `rd_xa_post`: from the allocator's continuation `Ea` in its region, under
  a frame condition the call hands it, to `.x13` (of `sJp`) in
  `wc_rodata`'s region, under any labelling placing `l` at the base;
- `hello1_rodata_post_tpW`: from `.x13` with the call's `%fs` base to
  `sXf`, given the region's base is the call's `%rsp`;
- `hello1_rodata_setupPW`: `hello1_rodata_setupW` with the allocation's
  continuation asked at `.x13`'s states (`hpost`) instead of at the
  allocator's landing.
-/
import Spike.Lib.X64Hello1RodataSetup

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.KeepTP (TP tpXa)
open Spike.Lib.X64.Flow.Ret0 (WcG)
open Spike.Lib.X64.Alloc (Call Ea Jfull)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

set_option linter.unusedSimpArgs false

section Xa

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- The frame record's saved `%rbp` cell is outside the allocator's region. -/
theorem aR_off_neg8 : ¬ (aR R).Off (-8 - -48) := fun h => by
  have := h.2.2
  simp [Region.callee] at this

/-- The return address's cell is outside the allocator's region. -/
theorem aR_off_0 : ¬ (aR R).Off (0 - -48) := fun h => by
  have := h.2.2
  simp [Region.callee] at this

omit [Executable.ValidLayout exe] in
/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.x13`**: a
state at the continuation `Ea` of label `l`, base `b`, in the allocator's
region, under a frame condition `F'` the call hands it (as in
`hello1_rodata_setupW`'s `hxa`), is at `.x13` of `sJp lbl'` in
`wc_rodata`'s region under `F`, for every labelling `lbl'` placing `l` at
`b`. -/
theorem rd_xa_post {F0 : MachineData → Prop} {g : WcG} {q : AG ms (_root_.Executable.labels exe).label}
    {F' : MachineData → Prop} {l : WeakMem.AllocLabel} {b w : Nat} {lbl' : WeakMem.AllocLabel → Option Nat}
    (hl : lbl' l = some b) (hFF : ∀ m, F' m → F m)
    (hkeep : ∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
      (rNL (_root_.Executable.labels exe).label R (sJ0 (_root_.Executable.labels exe).label ms F0 g)
        (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 g)) .call).J σC c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 8 mC m)
    {s : State} {c : Ctl} (h : At exe endPc (aR R) F' (Ea ms q.1 l b w) s c) :
    At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl' ms g R⟩ s c := by
  have h' := at_leave (R := R) (F := F) (kb := -48) (lo' := -160) (hi' := 8)
    (P := fun σ => ∃ c0,
      (rNL (_root_.Executable.labels exe).label R (sJ0 (_root_.Executable.labels exe).label ms F0 g)
        (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 g)) .call).J σ c0 ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC, hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, ?_⟩
  · rw [hpc]
    show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".Lwc_rodata.x13"
    rw [← h2.2.2.1]
    show Int64.ofBitVec (σC.slot (-48)) = _
    rw [h1.2.2.2.2.2, int64_ofBitVec_toBitVec]
  · obtain ⟨⟨σe, ⟨⟨c', ⟨⟨-, hfp, hra, -, -⟩, -⟩⟩, hc⟩, h0, h8⟩, hbp, -⟩ := h1
    have hq : q.1.c0 = rdCN := h2.1 ▸ hc
    obtain ⟨hx, hτ, he', hn'⟩ := rdQ_facts q.2 hq
    obtain ⟨ini, old, hcl, hx0, hb, hold, hfpx, -⟩ := hJx
    have hb' : b = ms.heap + 16 * old + ms.off 2 τ8 := by rw [← hn', ← hτ]; exact hb
    have hold' : old + ms.units 2 τ8 ≤ ms.cells := by rw [← hn', ← hτ]; exact hold
    refine ⟨l, ini, ⟨b, old, hl, hx0, hb', hold', ?_, ?_, ?_⟩, ?_⟩
    · show (leave (aR R) (-48) σC σx).slot (-8) = g.fp
      simp only [leave]
      rw [ite_eq_right aR_off_neg8]
      exact h8.trans hfp
    · show (leave (aR R) (-48) σC σx).slot 0 = g.ra
      simp only [leave]
      rw [ite_eq_right aR_off_0]
      exact h0.trans hra
    · show σx.regs.rbp.toBitVec = _
      rw [hfpx, ← h2.2.1]
      exact hbp
    · rw [hq, hx, hτ, he', hn'] at hcl
      exact hcl

/-- **`wc_rodata` from `.x13` to the setup block's return, the `%fs` base
kept**: from `.x13` of `sJp lbl` with the call's `%fs` base to `sXf`, in a
region of depth 40 whose base is the call's `%rsp` (`hL`), the buffer's
words unmapped under `F` (`hbuf`), the states in `W`, none moved by `K`
(`hWpost`); `rdQ`'s premises (`hQ`) bound the arena. -/
theorem hello1_rodata_post_tpW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi) (g : WcG) (hL : R.addr 0 = g.sp)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g R) (sJp' lbl ms g R) (sJh1 lbl ms g R) (sJ2 lbl ms g R)
      (sJ2' lbl ms g R) (sJh2 lbl ms g R) (sJ4 lbl ms g R)) :
    SegW W K p lbl ms
      (fun s c => At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", ⟨-40, []⟩,
        sJp lbl ms g R⟩ s c ∧ TP g.tp s)
      (At exe endPc R F (sXf lbl ms g)) := by
  let lab := (_root_.Executable.labels exe).label
  let ms' := tpXa ms g.tp
  have hA8 : ∀ σ0 l, RdF lbl ms g R σ0 l → (σ0.regs.rax.toBitVec + 8#64).toNat = σ0.regs.rax.toNat + 8 := by
    rintro σ0 l ⟨A, old, -, hx0, hA, hold, -, -, -⟩
    have hoff : ms.off 2 τ8 = 8 := by
      have h := hQ.off
      simp only [rdQ] at h
      rw [h]; decide
    have hcells := hQ.cells
    have hroom := hQ.room
    rw [BitVec.toNat_add, show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]
    simp only [BitVec.toNat_ofNat]
    omega
  have hpost : SegW (NoSetFsW W K) K p lbl ms'
      (At exe endPc R F ⟨lab ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl ms g R⟩)
      (At exe endPc R F (sX lbl ms g)) := by
    refine hello1_rodata_post_runW hp hend hF hR (by omega) hhi (show SO.le ⟨8, []⟩ ⟨8, []⟩ = true by decide)
      (RdPostLW.noSetFs hp hend hWpost)
      ?hbp ?hra ?hmem ?hr0 ?h1 ?h2 ?hr2 ?h3 ?h4 ?hedge
    case hbp =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, -, hbp⟩, -⟩
      exact hbp
    case hra =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, h0, -⟩, -⟩
      show Int64.ofBitVec g.ra = _
      rw [h0]
    case hmem =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, hx0, hA, hold, -, -, -⟩, -⟩ i hi m hm
      rcases hi with rfl | rfl
      · have := hbuf old hold 0 (.inl rfl) m hm
        rw [bAddr_rax_0]
        rw [show σ0.regs.rax.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 0) by
          apply BitVec.eq_of_toNat_eq
          rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0, BitVec.toNat_ofNat]
          have hroom := hQ.room
          have hcells := hQ.cells
          have hoff : ms.off 2 τ8 = 8 := by
            have h := hQ.off
            simp only [rdQ] at h
            rw [h]; decide
          omega]
        exact this
      · have := hbuf old hold 8 (.inr rfl) m hm
        rw [bAddr_rax_8]
        rw [show σ0.regs.rax.toBitVec + 8#64 = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 8) by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]
          have hroom := hQ.room
          have hcells := hQ.cells
          have hoff : ms.off 2 τ8 = 8 := by
            have h := hQ.off
            simp only [rdQ] at h
            rw [h]; decide
          omega]
        exact this
    case hr0 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC1 l ini, .single (rdCA_store (p := p) (ini := ini) hl).1, l, ini, hRF, rfl⟩
    case h1 =>
      rintro σ0 c ⟨l, ini, hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, w', hRF, rfl⟩⟩
      rw [bAddr_rax_0, show σ0.regs.rax.toBitVec.toNat = A + 8 * 0 by
        rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]; omega]
      exact hv
    case h2 =>
      rintro σ0 c ⟨l, ini, w', hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, w', hRF, (rdC1_next l ini w').symm⟩
      · rw [bAddr_rax_0, show σ0.regs.rax.toBitVec.toNat = A + 8 * 0 by
          rw [show σ0.regs.rax.toBitVec.toNat = σ0.regs.rax.toNat from rfl, hx0]; omega]
        exact hv
      · rw [show (rpK1.setWidth 128).toNat = rdK1 by decide]; exact hk
    case hr2 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      obtain ⟨A, old, hl, -⟩ := id hRF
      exact ⟨rdC3 l ini wo0, .single (rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl).1, l, ini, wo0, hRF, rfl⟩
    case h3 =>
      rintro σ0 c ⟨l, ini, wo0, hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, hh, -, -⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, hx, ?_, hh, fun r w' _ _ => ⟨l, ini, wo0, w', hRF, rfl⟩⟩
      rw [bAddr_rax_8, h8, hx0]
      exact hv
    case h4 =>
      rintro σ0 c ⟨l, ini, wo0, w', hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, wo0, w', hRF, (rdC3_next l ini wo0 w').symm⟩
      · rw [bAddr_rax_8, h8, hx0]
        exact hv
      · rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk
    case hedge =>
      rintro σ0 c ⟨l, ini, wo0, wo1, ⟨A, old, hl, hx0, hA, hold, h8, -, -⟩, rfl⟩ σ' hax hdx hcx hsi hbp -
      refine ⟨rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1,
        ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, hdx, hcx, hsi⟩, hbp.trans h8⟩
      show σ'.regs.rax.toBitVec.toNat = A
      rw [hax]; exact hx0
  refine (SegW.keepTPN (t := g.tp) hK hpost).mono_post fun s c ⟨⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, hbp⟩, ht⟩ =>
    ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, hbp, ?_, ?_⟩
  · have := hAb.so .rsp 8 rfl
    rw [addr8, hL] at this
    exact this
  · rw [← hAb.regs]; exact ht

/-- **`hello1_rodata_setupW` with the allocation's continuation at
`.x13`**: a fresh label `l`'s allocation, landing at base `b`, continues in
`ms.xa` whenever the state is at `.x13` of `sJp lbl'` for every labelling
`lbl'` placing `l` at `b`, at the call's `%fs` base, the region's base the
call's `%rsp` (`hpost`; `hello1_rodata_post_tpW` runs from there). -/
theorem hello1_rodata_setupPW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hK : ms.K = some Scc.Sem.X64.abi) (hF : FStable R F) (hR : R.OK)
    (hlo : R.lo ≤ -240) (hhi : 8 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hpost : ∀ l b w s c, lbl l = none → R.addr 0 = g.sp →
      (∀ lbl' : WeakMem.AllocLabel → Option Nat, lbl' l = some b →
        At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_rodata.x13", ⟨-40, []⟩, sJp lbl' ms g R⟩
          s c) →
      TP g.tp s → ms.xa l b w s c)
    (hWpre : RdPreW W K exe endPc R F ms (sJ0 (_root_.Executable.labels exe).label ms F0 g)
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 g)))
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g R) (sJp' lbl ms g R) (sJh1 lbl ms g R) (sJ2 lbl ms g R)
      (sJ2' lbl ms g R) (sJh2 lbl ms g R) (sJ4 lbl ms g R))
    (hstub : ∀ m0 σC c0, σC.regs.rdi.toBitVec = 2#64 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-208 - 8) (-24) 16)
        (fun m => F m ∧ CKept R (-208 - 8) (-24) 16 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (Spike.Lib.X64.Rt.uN0 (_root_.Executable.labels exe).label ms F0 "wc_rodata" 32 g))
      (At exe endPc R F (sXf lbl ms g)) := by
  refine (SegW.of_imp (L := R.addr 0 = g.sp) fun hL => hello1_rodata_setupW hp hend hK hF hR hlo hhi hFF g
    hc0 hQ hu hmem hbuf (fun q F' hFF' hkeep l b w s c hl hAt htp =>
      hpost l b w s c hl hL (fun lbl' hl' => rd_xa_post hl' hFF' hkeep hAt) htp) hWpre hWpost hstub).mono_pre
    fun s c h => ⟨h, ?_⟩
  obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨hc, hfp, hra, hsp, htp⟩, hl⟩ := id h
  rw [← hsp]; exact (hAb.so .rsp 0 rfl).symm

end Xa

end Spike.Lib.X64.Flow.Hello1

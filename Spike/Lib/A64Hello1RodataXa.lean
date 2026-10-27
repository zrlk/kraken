/-
**`wc_rodata`'s allocation continuation on AArch64**: a fresh label's
landing in the allocator is at `wc_rodata`'s `.sp0` for any placement of the
label at the landing's base, and from there the rest of `wc_rodata` runs to
the setup block's return (`Spike/Lib/A64Hello1RodataSetup.lean`), the thread
pointer kept.

- `aR_off_neg16`, `aR_off_neg8`: the frame record's cells lie outside the
  allocator's region;
- `rd_xa_post`: from the allocator's continuation `Ea` in its region, under
  a frame condition the call hands it, to `.sp0` (`pN .s0` of `sJp`) in
  `wc_rodata`'s region, under any labelling placing `l` at the base;
- `hello1_rodata_post_tpW`: from `.sp0` with the call's thread pointer to
  `sXf`, given the region's base is the call's `sp`;
- `hello1_rodata_setupPW`: `hello1_rodata_setupW` with the allocation's
  continuation asked at `.sp0`'s states (`hpost`) instead of at the
  allocator's landing.
-/
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow.Ret0 (WcG)
open Spike.Lib.A64.Alloc (Call Ea Jfull)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

set_option linter.unusedSimpArgs false

section Xa

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- The frame record's `fp` cell is outside the allocator's region. -/
theorem aR_off_neg16 : ¬ (aR R).Off (-16 - -48) := fun h => by
  have := h.2.2
  simp [Region.callee] at this

/-- The frame record's `lr` cell is outside the allocator's region. -/
theorem aR_off_neg8 : ¬ (aR R).Off (-8 - -48) := fun h => by
  have := h.2.2
  simp [Region.callee] at this

omit [Kraken.Executable.ValidLayout exe] in
/-- **The allocator's fresh-label landing is at `wc_rodata`'s `.sp0`**: a
state at the continuation `Ea` of label `l`, base `b`, in the allocator's
region, under a frame condition `F'` the call hands it (as in
`hello1_rodata_setupW`'s `hxa`), is at `pN .s0` of `sJp lbl'` in
`wc_rodata`'s region under `F`, for every labelling `lbl'` placing `l` at
`b`. -/
theorem rd_xa_post {F0 : MachineData → Prop} {g : WcG} {q : AG ms (_root_.Executable.labels exe).label}
    {F' : MachineData → Prop} {l : WeakMem.AllocLabel} {b w : Nat} {lbl' : WeakMem.AllocLabel → Option Nat}
    (hl : lbl' l = some b) (hFF : ∀ m, F' m → F m)
    (hkeep : ∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
      (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
        (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .call).J σC c ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m)
    {s : State} {c : Ctl} (h : At exe endPc (aR R) F' (Ea ms q.1 l b w) s c) :
    At exe endPc R F (pN (_root_.Executable.labels exe).label (sJp lbl' ms g) (sJh1 lbl' ms g) (sJ2 lbl' ms g)
      (sJh2 lbl' ms g) (sJ4 lbl' ms g) .s0) s c := by
  have h' := at_leave (R := R) (F := F) (kc := -48) (lo' := -160) (hi' := 0)
    (P := fun σ => ∃ c0,
      (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
        (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .call).J σ c0 ∧
      (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σ) c0)
    rfl (fun m hm => by
      obtain ⟨mC, σ, c0, hA, h1, h2, hK⟩ := hkeep m hm
      exact ⟨hFF m hm, mC, σ, _, hK, hA, c0, h1, h2⟩) h
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, σx, σC, hJx, ⟨c0, h1, h2⟩, rfl⟩ := h'
  refine ⟨he, hn, hdc, ?_, _, hA, hD, ?_⟩
  · rw [hpc]
    show Int64.ofBitVec q.1.ra = (_root_.Executable.labels exe).label ".L18_wc_rodata.sp0"
    rw [← h2.2.2.1]
    show Int64.ofBitVec σC.regs.X30.toBitVec = _
    rw [h1.2.2.2.2, int64_ofBitVec_toBitVec]
  · obtain ⟨⟨σe, ⟨⟨c', ⟨⟨-, h29, h30, -, -⟩, -⟩⟩, hc⟩, h16, h8⟩, -⟩ := h1
    have hq : q.1.c0 = rdCN := h2.1 ▸ hc
    obtain ⟨hx, hτ, he', hn'⟩ := rdQ_facts q.2 hq
    obtain ⟨ini, old, hcl, hx0, hb, hold, -, -⟩ := hJx
    have hb' : b = ms.heap + 16 * old + ms.off 2 τ8 := by rw [← hn', ← hτ]; exact hb
    have hold' : old + ms.units 2 τ8 ≤ ms.cells := by rw [← hn', ← hτ]; exact hold
    refine ⟨l, ini, ⟨b, old, hl, hx0, hb', hold', ?_, ?_⟩, ?_⟩
    · show (leave (aR R) (-48) σC σx).slot (-16) = g.fp
      simp only [leave]
      rw [ite_eq_right aR_off_neg16]
      exact h16.trans h29
    · show (leave (aR R) (-48) σC σx).slot (-8) = g.ra
      simp only [leave]
      rw [ite_eq_right aR_off_neg8]
      exact h8.trans h30
    · rw [hq, hx, hτ, he', hn'] at hcl
      exact hcl

/-- **`wc_rodata` from `.sp0` to the setup block's return, the thread
pointer kept**: from `pN .s0` of `sJp lbl` with the call's thread pointer
to `sXf`, in a region of depth 48 whose base is the call's `sp` (`hL`), the
buffer's words unmapped under `F` (`hbuf`), the states in `W`, none moved by
`K` (`hWpost`); `rdQ`'s premises (`hQ`) bound the arena. -/
theorem hello1_rodata_post_tpW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (g : WcG) (hL : R.addr 0 = g.sp)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g) (sJp' lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g)
      (sJ2' lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g)) :
    SegW W K p lbl ms
      (fun s c => At exe endPc R F (pN (_root_.Executable.labels exe).label (sJp lbl ms g) (sJh1 lbl ms g)
        (sJ2 lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g) .s0) s c ∧ TP g.tp s)
      (At exe endPc R F (sXf lbl ms g)) := by
  let lab := (_root_.Executable.labels exe).label
  let ms' := tpXa ms g.tp
  have hoff : ms.off 2 τ8 = 8 := by
    have h := hQ.off
    simp only [rdQ] at h
    rw [h]; decide
  have hcells := hQ.cells
  have hroom := hQ.room
  have hA8 : ∀ σ0 l, RdF lbl ms g σ0 l → (σ0.regs.X0.toBitVec + 8#64).toNat = σ0.regs.X0.toNat + 8 := by
    rintro σ0 l ⟨A, old, -, hx0, hA, hold, -, -⟩
    rw [BitVec.toNat_add, show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]
    simp only [BitVec.toNat_ofNat]
    omega
  have hpost : SegW (NoMsrW W K) K p lbl ms'
      (At exe endPc R F (pN lab (sJp lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g) .s0))
      (At exe endPc R F (sX lbl ms g)) := by
    refine hello1_rodata_post_runW hp hend hF hR hal hlo hhi rfl (RdPostLW.noMsr hp hend hWpost)
      ?hra ?hmem ?hr0 ?h1 ?h2 ?hr2 ?h3 ?h4 ?hedge
    case hra =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, -, -, -, -, h8⟩, -⟩
      show Int64.ofBitVec g.ra = _
      rw [h8]
    case hmem =>
      rintro σ0 c ⟨l, ini, ⟨A, old, -, hx0, hA, hold, -, -⟩, -⟩ i hi m hm
      rcases hi with rfl | rfl
      · have := hbuf old hold 0 (.inl rfl) m hm
        rw [rAddr_x0_0]
        rw [show σ0.regs.X0.toBitVec = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 0) by
          apply BitVec.eq_of_toNat_eq
          rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0, BitVec.toNat_ofNat]
          omega]
        exact this
      · have := hbuf old hold 8 (.inr rfl) m hm
        rw [rAddr_x0_8]
        rw [show σ0.regs.X0.toBitVec + 8#64 = BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + 8) by
          apply BitVec.eq_of_toNat_eq
          rw [BitVec.toNat_add, show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0,
            BitVec.toNat_ofNat, BitVec.toNat_ofNat]
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
      rw [rAddr_x0_0, show σ0.regs.X0.toBitVec.toNat = A + 8 * 0 by
        rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]; omega]
      exact hv
    case h2 =>
      rintro σ0 c ⟨l, ini, w', hRF, rfl⟩
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdCA_store (p := p) (ini := ini) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, w', hRF, (rdC1_next l ini w').symm⟩
      · rw [rAddr_x0_0, show σ0.regs.X0.toBitVec.toNat = A + 8 * 0 by
          rw [show σ0.regs.X0.toBitVec.toNat = σ0.regs.X0.toNat from rfl, hx0]; omega]
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
      rw [rAddr_x0_8, h8, hx0]
      exact hv
    case h4 =>
      rintro σ0 c ⟨l, ini, wo0, w', hRF, rfl⟩
      have h8 := hA8 σ0 l hRF
      obtain ⟨A, old, hl, hx0, -⟩ := id hRF
      obtain ⟨-, hx, hv, -, hev, hk⟩ := rdC2_store (p := p) (ini := ini) (wo0 := wo0) hl
      refine ⟨_, _, _, _, _, _, _, w', hx, ?_, rfl, hev, ?_, l, ini, wo0, w', hRF, (rdC3_next l ini wo0 w').symm⟩
      · rw [rAddr_x0_8, h8, hx0]
        exact hv
      · rw [show (rpK2.setWidth 128).toNat = rdK2 by decide]; exact hk
    case hedge =>
      rintro σ0 c ⟨l, ini, wo0, wo1, ⟨A, old, hl, hx0, hA, hold, h16, h8⟩, rfl⟩ σ' h0 h1 h2 h3 h29 h30
      refine ⟨rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1, ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, h1, h2, h3⟩,
        h29.trans h16, h30.trans h8⟩
      show σ'.regs.X0.toBitVec.toNat = A
      rw [h0]; exact hx0
  refine (SegW.keepTPN (t := g.tp) hK hpost).mono_post fun s c ⟨⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, h29, h30⟩, ht⟩ =>
    ⟨he, hn, hdc, hpc, σ, hAb, hD, hJ, h29, h30, ?_, ?_⟩
  · have := hAb.so .SP 0 rfl
    rw [← hL]; exact this
  · rw [← hAb.regs]; exact ht

/-- **`hello1_rodata_setupW` with the allocation's continuation at
`.sp0`**: a fresh label `l`'s allocation, landing at base `b`, continues in
`ms.xa` whenever the state is at `.sp0` of `sJp lbl'` for every labelling
`lbl'` placing `l` at `b`, at the call's thread pointer, the region's base
the call's `sp` (`hpost`; `hello1_rodata_post_tpW` runs from there). -/
theorem hello1_rodata_setupPW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hK : ms.K = some Scc.Sem.A64.abi) (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ -256) (hhi : 0 ≤ R.hi) {F0 : MachineData → Prop} (hFF : ∀ m, F m → F0 m)
    (g : WcG) (hc0 : g.c0 = rdC0)
    (hQ : rdQ.OK ms (_root_.Executable.labels exe).label) (hu : ms.units 2 τ8 = 3)
    (hmem : ∀ q : Call, q.OK ms (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hbuf : ∀ old : Nat, old + ms.units 2 τ8 ≤ ms.cells → ∀ i : Nat, (i = 0 ∨ i = 8) → ∀ m, F m →
      Mem.loadInt m.dmem (BitVec.ofNat 64 (ms.heap + 16 * old + ms.off 2 τ8 + i)) 8 = none)
    (hpost : ∀ l b w s c, lbl l = none → R.addr 0 = g.sp →
      (∀ lbl' : WeakMem.AllocLabel → Option Nat, lbl' l = some b →
        At exe endPc R F (pN (_root_.Executable.labels exe).label (sJp lbl' ms g) (sJh1 lbl' ms g)
          (sJ2 lbl' ms g) (sJh2 lbl' ms g) (sJ4 lbl' ms g) .s0) s c) →
      TP g.tp s → ms.xa l b w s c)
    (hWpre : RdPreW W K exe endPc R F ms (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
      (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)))
    (hWpost : RdPostLW W K exe endPc R F (sJp lbl ms g) (sJp' lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g)
      (sJ2' lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g))
    (hstub : ∀ m0 σC c0, σC.regs.X0 = 2 →
      (∃ q : Call, q.OK ms (_root_.Executable.labels exe).label ∧ q.c0 = rdCN ∧ Jfull ms q c0) →
      Abort.Disp.StubHW W K p lbl ms exe endPc (R.callee (-208) (-48) 0)
        (fun m => F m ∧ CKept R (-208) (-48) 0 m0 m ∧ Abs R ⟨-208, []⟩ m0 σC) c0) :
    SegW W K p lbl ms
      (At exe endPc R F (Spike.Lib.A64.Rt.uN0 (_root_.Executable.labels exe).label ms F0 exe endPc "wc_rodata" 48 g))
      (At exe endPc R F (sXf lbl ms g)) := by
  refine (SegW.of_imp (L := R.addr 0 = g.sp) fun hL => hello1_rodata_setupW hp hend hK hF hR hal hlo hhi hFF g
    hc0 hQ hu hmem hbuf (fun q F' hFF' hkeep l b w s c hl hAt htp =>
      hpost l b w s c hl hL (fun lbl' hl' => rd_xa_post hl' hFF' hkeep hAt) htp) hWpre hWpost hstub).mono_pre
    fun s c h => ⟨h, ?_⟩
  obtain ⟨he, hn, hdc, hpc, σ, hAb, hD, ⟨hc, h29, h30, hsp, htp⟩, hl⟩ := id h
  rw [← hsp]; exact (hAb.so .SP 0 rfl).symm

end Xa

end Hello1

end Spike.Lib.A64.Flow

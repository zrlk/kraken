/-
**`wc_rodata` from its call to its return through the generic setup
composition** (a regression check of `Spike/Lib/A64SetupW.lean`):
`hello1_rodata_setupW`'s statement re-derived by `Setup.setup_callW`, the
body a `Setup.chainW` walk of the allocation (`Setup.alloc_stepW`, the
entry block `rdE` and the call of `scc_rt_alloc`) and the lane stores with
the epilogue from `.sp0` (`hello1_rodata_post_runW`).

- `nbJc_rN`: the call node of `alloc_stepW` after `rdE` is `rN`'s;
- `nbX_sJp`: the allocator's return of `alloc_stepW` is `sJp`'s;
- `hello1_rodata_setupGW`: `hello1_rodata_setupW` through `setup_callW`.
-/
import Spike.Lib.A64SetupW
import Spike.Lib.A64Hello1RodataSetup

namespace Spike.Lib.A64.Flow

namespace Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib
open Scc.Cert.Rt.A64 (Lays endOf label_labelGap)
open Spike.Lib.A64.KeepTP (TP tpXa)
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk WcG limA tcbA_limA)
open Spike.Lib.A64.Alloc (Call AllocW Ea Jfull mOf)
open Spike.Lib.A64.Flow.NewBuf (allocAbortDepth allocAbortDepth_48 nbX nbJc NBX)
open Spike.Lib.A64.Flow.Setup (entJ sEn sRet sAb chainW alloc_stepW setup_callW)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdCA rdC1 rdC2 rdC3 rdC4 rdRet eW0 τ8 rdK1 rdK2 rdC0_run rdCN_newBuf
  rdCA_store rdC2_store rdC1_next rdC3_next rdC4_run)

set_option linter.unusedSimpArgs false

section Proof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- `rdE`'s return address: `.sp0`, right after the call. -/
theorem rdE_x30 (hp : Lays exe SccCode.hello1Prog) (σ : AS) :
    (arun (_root_.Executable.labels exe).label rdE
      ⟨(_root_.Executable.labels exe).label ".L18_wc_rodata.0_entry", ⟨-48, []⟩, σ⟩).σ.regs.X30.toBitVec =
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0").toBitVec := by
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  have e4 := label_labelGap hp hin.2
  have e4' : (_root_.Executable.labels exe).label ".L18_wc_rodata.sp0" =
      (_root_.Executable.labels exe).label ".L18_wc_rodata.0_entry" + Int64.ofNat (4 * 4) := e4
  rw [rdE_run, e4']
  show BitVec.ofInt 64 _ = _
  rw [Ret0.ofInt_bmod]
  simp only [BitVec.ofInt_add, Spike.Lib.int64_ofInt_toInt, Int64.toBitVec_add, BitVec.add_assoc]
  rfl

/-- **The call node after `rdE` is `rN`'s**: the frame record as at the
entry, the allocation's arguments and the return address `.sp0`. -/
theorem nbJc_rN (hp : Lays exe SccCode.hello1Prog) {J : AS → Ctl → Prop} {σ : AS} {c : Ctl}
    (h : nbJc (_root_.Executable.labels exe).label rdE
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.0_entry") ⟨-48, []⟩ (entJ J) σ c) :
    (rN (_root_.Executable.labels exe).label J .call).J σ c := by
  obtain ⟨σ0, ⟨σe, hJ, h16, h8⟩, rfl⟩ := h
  have hx30 := rdE_x30 hp σ0
  rw [rdE_run] at hx30 ⊢
  exact ⟨⟨σe, hJ, h16, h8⟩, rfl, rfl, rfl, hx30⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The allocator's return after `rdE` is `sJp`'s**: the frame record
outside the allocator's region kept from the call, the source past the
allocation. -/
theorem nbX_sJp (hlo : R.lo ≤ -16) (hhi : 0 ≤ R.hi)
    {F0 : MachineData → Prop} {g : WcG} {t : UInt64} {σ : AS} {c : Ctl}
    (h : (nbX (tpXa ms t) (_root_.Executable.labels exe).label lbl R 48
      ((_root_.Executable.labels exe).label ".L18_wc_rodata.sp0")
      (nbJc (_root_.Executable.labels exe).label rdE
        ((_root_.Executable.labels exe).label ".L18_wc_rodata.0_entry") ⟨-48, []⟩
        (entJ (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)))) .ret).J σ c) :
    sJp lbl ms g σ c := by
  obtain ⟨q, ⟨σC, ⟨σ0, ⟨σe, hJ, h16, h8⟩, hσC⟩, hsl⟩, hE⟩ := h
  have hk : ∀ k : Int, (k = -16 ∨ k = -8) → σ.slot k = σ0.slot k := by
    rintro k hk
    rw [hsl k ⟨by omega, by omega, by omega⟩ (by simp only [Region.callee, Region.Off]; omega), hσC, rdE_run]
  refine sp0_sJp (t := t) ⟨q, ⟨σe, hJ, ?_, ?_⟩, hE⟩
  · rw [hk (-16) (.inl rfl)]; exact h16
  · rw [hk (-8) (.inr rfl)]; exact h8

/-- **`hello1_rodata_setupW` through the generic setup composition**: the
same statement, by `setup_callW` with the body walked by `chainW` (the
allocation by `alloc_stepW`, then `.sp0` to the return). -/
theorem hello1_rodata_setupGW {W : Frag isaLSE2} {K : State → State → Prop}
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
    (hxa : ∀ q : AG ms (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop, (∀ m, F' m → F m) →
      (∀ m, F' m → ∃ mC σC c, Abs R ⟨-48, []⟩ mC σC ∧
        (rNL (_root_.Executable.labels exe).label (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)
          (sJ1 (sJ0 (_root_.Executable.labels exe).label ms F0 exe endPc g)) .call).J σC c ∧
        (Alloc.N (_root_.Executable.labels exe).label ms q.1 .e).J (enter (-48) σC) c ∧ CKept R (-48) (-160) 0 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR R) F' (Ea ms q.1 l b w) s c → TP g.tp s → ms.xa l b w s c)
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
  let lab := (_root_.Executable.labels exe).label
  let J0 := sJ0 lab ms F0 exe endPc g
  let ms' := tpXa ms g.tp
  let Ab : Ctl → Prop := fun c => ∃ q : Call, q.OK ms lab ∧ q.c0 = rdCN ∧ Jfull ms q c
  have hin := hello1_rdEIn
  simp only [rdEIn, Bool.and_eq_true] at hin
  have hWN := RdPreW.noMsr hp hend hWpre
  -- the bounds of the buffer's words
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
  -- the allocation: `rdE` and the call
  have hal1 : SegW (NoMsrW W K) K p lbl ms'
      (At exe endPc R F ⟨lab ".L18_wc_rodata.0_entry", ⟨-48, []⟩, entJ J0⟩)
      (fun s c => At exe endPc R F ⟨lab ".L18_wc_rodata.sp0", ⟨-48, []⟩, sJp lbl ms g⟩ s c ∨
        At exe endPc R F (sAb lab 48 Ab) s c) := by
    refine alloc_stepW (J1 := entJ (sJ1 J0)) hp hend hello1_alloc hF hR hal (by decide)
      (by rw [allocAbortDepth_48]; omega) (by omega) (by simp [rdE]) rdE_ok (by omega) hhi
      (code_of hp hend hin.1 (ofNat4_zero _)) (fun σ => by rw [rdE_run]; exact ⟨rfl, rfl⟩) ?hloc ?hq
      (fun σ c _ => rdE_x30 hp σ) (fun q hq a ha m hm => hmem q (Setup.callOK_untp hq) a ha m hm) ?hxa hWN.e
      (fun q hok hq => allocW_mono (allocW_tp (hWN.alloc q (Setup.callOK_untp hok) hq))
        fun _ ⟨h1, h2, mC, σC, c, hA, hJ, hN, hK⟩ =>
        ⟨h1, h2, mC, σC, c, hA, nbJc_rN hp hJ, hN, hK⟩)
      (fun σ c h => nbX_sJp (by omega) hhi h) ?hab
    case hloc =>
      rintro σ c ⟨σe, hJe, h16, h8⟩
      exact ⟨rdCN, by rw [hJe.1.1, hc0]; exact rdC0_run, σe, ⟨⟨c, hJe⟩, rfl⟩, h16, h8⟩
    case hq =>
      rintro σ c ⟨σe, ⟨-, rfl⟩, -⟩
      refine ⟨rdQ, Setup.callOK_tp hQ, rfl, ?_, ?_, ?_⟩ <;> rw [rdE_run]
      · rfl
      · rfl
      · show 3#64 = BitVec.ofNat 64 (ms.units 2 τ8)
        rw [hu]
    case hxa =>
      intro q F' h1 h2 l b w s c hl hAt htp
      refine hxa ⟨q.1, Setup.callOK_untp q.2⟩ F' h1 (fun m hm => ?_) l b w s c hl hAt htp
      obtain ⟨mC, σC, c', hA, hJ, hN, hC⟩ := h2 m hm
      exact ⟨mC, σC, c', hA, nbJc_rN hp hJ, hN, hC⟩
    case hab =>
      rintro c ⟨q, hf, σC, σ0, ⟨σe, ⟨-, hc⟩, -⟩, -⟩
      exact ⟨q.1, Setup.callOK_untp q.2, hc, hf⟩
  -- from `.sp0` to the return
  have hpost : SegW (NoMsrW W K) K p lbl ms'
      (At exe endPc R F (pN lab (sJp lbl ms g) (sJh1 lbl ms g) (sJ2 lbl ms g) (sJh2 lbl ms g) (sJ4 lbl ms g) .s0))
      (At exe endPc R F (sX lbl ms g)) := by
    refine hello1_rodata_post_runW hp hend hF hR hal (by omega) hhi rfl (RdPostLW.noMsr hp hend hWpost)
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
      refine ⟨rdRet l ini wo0 wo1, rdC4_run l ini wo0 wo1,
        ⟨l, ini, wo0, wo1, A, old, rfl, hl, ?_, hA, hold, h1, h2, h3⟩, h29.trans h16, h30.trans h8⟩
      show σ'.regs.X0.toBitVec.toNat = A
      rw [h0]; exact hx0
  -- the walk: the allocation, then `.sp0` to the return
  have hbody : SegW (NoMsrW W K) K p lbl ms' (At exe endPc R F (sEn lab ".L18_wc_rodata.0_entry" 48 J0))
      (fun s c => At exe endPc R F (sRet (rdPostS lbl ms) g) s c ∨
        At exe endPc R F (sAb lab (48 : Int64).toInt Ab) s c) :=
    chainW (A := fun k => if k = 0 then At exe endPc R F ⟨lab ".L18_wc_rodata.0_entry", ⟨-48, []⟩, entJ J0⟩
      else At exe endPc R F ⟨lab ".L18_wc_rodata.sp0", ⟨-48, []⟩, sJp lbl ms g⟩) 1
      (fun k hk => by
        obtain rfl : k = 0 := by omega
        exact hal1)
      (hpost.mono_post fun _ _ h => .inl h)
  refine (setup_callW hp hend hK hello1_rodataPro (by decide) (by decide) hF hR hal
    (by show R.lo ≤ -allocAbortDepth 48 - 48; rw [allocAbortDepth_48]; omega) hhi hFF g hWpre.pro hbody
    (fun m0 σC c0 h2 hab => hstub m0 σC c0 h2 hab)).mono_post fun _ _ h => h

end Proof

/-! ## The hand chain at `rodata`'s source

The hand chain's post segment (`hello1_rodata_post_segW`, and `hello1_main_post_segW`,
`hello1_main_segW`, `hello1_main_segW_src` over it) asks the source at `.sp0` to be an exchange
site (`h1`), with no local step first; its pre segment (`hello1_rodata_pre_segW`) asks the
source at the entry to be the allocation (`hq`). At `rodata`'s source neither holds: the entry
`rdC0` is two local steps before the allocation (`rdC0_not_call`), and the allocator returns to
`rdCA`, one `asLanes` step before the exchange (`rdCA_not_xchgSite`). So with the entry at
`rdCN`, the premises force the allocator's return node to be empty (`hand_sp0_empty`).
`hello1_rodata_setupW` and the walk above take those steps (`hello1_rodata_post_runW`). -/

/-- `rodata`'s entry is no allocation: `let two = 2` comes first. -/
theorem rdC0_not_call {ms : MemSide isaLSE2} {lab : Label → Int64} {q : Call} (h : q.OK ms lab) :
    q.c0 ≠ rdC0 := by
  intro hc
  have ht := h.term
  rw [hc] at ht
  simp [rdC0, Spike.Lib.Hello1RodataSrc.rdBody] at ht

/-- The allocator's return `rdCA` is no exchange site: `asLanes` comes first. -/
theorem rdCA_not_xchgSite {l : WeakMem.AllocLabel} {ini : Nat} {x : String} {sa : WeakMem.Address} {u : Ty}
    {v : CoreTerm.At} {e : Expr} : ¬ XchgSite (rdCA l ini) x sa u v e := by
  rintro ⟨-, ⟨_, _, _, _, ht, -⟩ | ⟨_, _, _, _, _, _, _, _, _, ht, -⟩⟩ <;>
    simp [rdCA, Spike.Lib.Hello1RodataSrc.eW0] at ht

/-- **The allocator's returns from `rodata`'s allocation** are at `rdCA`. -/
theorem rXsp0_rdCA {ms : MemSide isaLSE2} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J0 : AS → Ctl → Prop} (hJ0 : ∀ σ c, J0 σ c → c = rdCN) {σ : AS} {c : Ctl}
    (h : (rX ms lab lbl J0 .sp0).J σ c) : ∃ l ini, c = rdCA l ini := by
  obtain ⟨q, ⟨σe, hJe, -, -⟩, l, ini, old, -, hcl, -⟩ := h
  have hc := hJ0 _ _ hJe
  obtain ⟨hx, hτ, he, hn⟩ := rdQ_facts q.2 hc
  exact ⟨l, ini, by rw [hcl, hc, hx, hτ, he, hn]; rfl⟩

/-- **The hand chain is empty at `.sp0` at `rodata`'s source**: with the entry at `rdCN`, an
invariant `Jp` at `.sp0` holding the allocator's returns (as `hello1_main_segW`'s `hret` asks)
and an exchange site at each of its controls (as `hello1_rodata_post_segW`'s `h1` asks), the
allocator's return node has no state. -/
theorem hand_sp0_empty {ms : MemSide isaLSE2} {lab : Label → Int64} {lbl : WeakMem.AllocLabel → Option Nat}
    {J0 Jp : AS → Ctl → Prop} {Q : AS → Ctl → String → WeakMem.Address → Ty → CoreTerm.At → Expr → Prop}
    (hJ0 : ∀ σ c, J0 σ c → c = rdCN) (hret : ∀ σ c, (rX ms lab lbl J0 .sp0).J σ c → Jp σ c)
    (h1 : ∀ σ0 c, Jp σ0 c → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : CoreTerm.At) (e : Expr),
      XchgSite c x sa u v e ∧ Q σ0 c x sa u v e) :
    ∀ σ c, ¬ (rX ms lab lbl J0 .sp0).J σ c := by
  intro σ c h
  obtain ⟨l, ini, rfl⟩ := rXsp0_rdCA hJ0 h
  obtain ⟨_, _, _, _, _, hx, -⟩ := h1 σ _ (hret σ _ h)
  exact rdCA_not_xchgSite hx

end Hello1

end Spike.Lib.A64.Flow

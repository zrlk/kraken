/-
**`wc_main` against `print`'s byte loop** (AArch64): `hello1_wcA_segW`
(`Spike/Lib/A64Hello1BodyA.lean`) with its source predicates taken from the
source's print loop (`Spike/Lib/PrintSrc.lean`), and its write system call
(`hsvc`) from the output row's segment, assumed (`EmitW`,
`Spike/Lib/A64PrintEmit.lean`).

The caller gives the source's arguments of `print` as functions of the
body's entry state `σ0`: the buffer word `pw σ0`, the slice length's word
`wm σ0` (value `m σ0`) and the byte count's word `wn σ0` (value `n σ0`).
Inside `print` with `k` bytes out the source is at `PrintC … k` (`prC`),
both for `Pr` and for `Qr` (a refused write justifies the abort from where
the source stands, by `hwe`).

What is derived here:

- `hcall`: from a local run to `print`'s body on a nonempty slice
  (`hentry`), `print_entry_run` and `printC_entry`;
- `hsvc`: `hsvc_of_emit`, its byte steps by `printC_load`, the row's load
  and emit (`hlb`, assumed) and `printC_next`; the count is below `2^63`
  by `wcC_x1_lt`, and the code is `hello1_print`'s `svc`;
- `hedge`: `print_done_run` at `k = printN n m = wcLen σ0` (`hN`), then the
  return (`hret`, assumed).

What stays assumed: the row (`hE`, with its byte step `BO` and abort
justification `WE` abstract), `BO`'s closure under local runs before and
after (`hpre`, `hpost`), the row's load-and-emit from `loadC` to `nextC`
(`hlb`), the `.svc` states inside `W` (`hWs`), `print`'s declaration `hd`,
and the source's runs into and out of `print` (`hentry`, `hret`).

`hello1_wcA_print_segW'` takes `hpre` and `hpost` from one fact of the
byte step, its closure under local runs (`LocalClosed`, `Spike/Lib/A64PrintCall.lean`).
-/
import Spike.Lib.A64Hello1BodyA
import Spike.Lib.A64PrintEmit
import Spike.Lib.PrintSrc

namespace Spike.Lib.A64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Ret0 (CallerCells LimOk)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.PrintSrc (PrintC loadC nextC printN printLD printBody print_entry_run printC_entry
  print_done_run printC_load printC_next)

/-- **`print`'s source predicate** on the body's entry state `σ0`: the
source at the top of `printL` with `k` bytes out (`PrintC`), on the
arguments the caller gives for `σ0`. -/
def prC (pw wn : AS → TermRun.Word) (n m : AS → Nat) (σ0 : AS) (k : Nat) (c : Ctl) : Prop :=
  PrintC (pw σ0) (wn σ0) (n σ0) (m σ0) k c

section PrintAt

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`wc_main` is one segment inside `W`** against `print`'s byte loop, in
any valid layout of `hello1Prog`: `hello1_wcA_segW` with `Pr = Qr = prC`
and its `hcall`, `hsvc`, `hedge` derived (see the module docstring). -/
theorem hello1_wcA_print_segW {W : Frag isaLSE2} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wm wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcAW W K exe endPc R F ms J0 (prC pw wn n m) (prC pw wn n m))
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hm : ∀ σ c, J0 σ c → σ.regs.X2.toBitVec.toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec σ.regs.X30.toBitVec)
    -- the source's `print`
    (hd : p.find? (·.name == "printL") = some printLD)
    (hN : ∀ σ0 c0, wcJ J0 σ0 c0 → wcLen σ0 = printN (n σ0) (m σ0))
    (hentry : ∀ σ c, wcJ J0 σ c → ∃ c1, LocalRun p c c1 ∧
      c1 = ⟨printBody, [("a", Hello1Src.sliceTy, [pw σ, wm σ, wn σ])], none⟩ ∧
      (wm σ).val = .num (m σ) ∧ m σ ≠ 0 ∧ (wn σ).val = .num (n σ))
    (hret : ∀ σ0 c0, wcJ J0 σ0 c0 → ∀ env,
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ0 k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p ⟨.ret .unit, env, none⟩ c' ∧ x.J σ' c')
    -- the output row, assumed
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi)
    (hpre : ∀ s a c c' Φ, LocalRun p c c' → BO s a c' Φ → BO s a c Φ)
    (hpost : ∀ s a c (Φ Ψ : Ctl → Prop), BO s a c Φ → (∀ c1, Φ c1 → ∃ c2, LocalRun p c1 c2 ∧ Ψ c2) →
      BO s a c Ψ)
    (hWs : ∀ (F' : MachineData → Prop) (σC : AS) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) σC .svc) s c → W s c ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σ0 c0, wcJ J0 σ0 c0 → ∀ (F' : MachineData → Prop) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) (wcC (_root_.Executable.labels exe).label σ0) .svc) s c →
      ∀ k j, k + j < wcLen σ0 →
      BO s (((wcC (_root_.Executable.labels exe).label σ0).regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j)
        (loadC (pw σ0) (wn σ0) (m σ0) (k + j)) (fun c => ∃ mw b, c = nextC (pw σ0) (wn σ0) (m σ0) (k + j) mw b))
    (hwe : ∀ (F' : MachineData → Prop) (σC : AS) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) σC .svc) s c →
      ∀ k c1, pP (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m) σC k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label (wcJ J0)
        (prC pw wn n m) x y) s c) := by
  refine hello1_wcA_segW hp hend hF hR hal hlo hhi ho hW hlim hm hra ?_ ?_ ?_
  · -- `hcall`: into `print`, then to the top of `printL`
    intro σ c hJ
    obtain ⟨c1, r, rfl, hwm, hm0, hwn⟩ := hentry σ c hJ
    exact ⟨_, r.trans (print_entry_run hd hwm hm0).toLocalRun, printC_entry hwn hm0⟩
  · -- `hsvc`: the output row's segment
    intro F' hF' _ σC _
    refine PrintA.hsvc_of_emit hE hK hF' ?_ ?_ (hWs F' σC) (fun _ _ h => h) ?_ (hwe F' σC)
    · rintro k c ⟨σ0, c0, hJ, rfl, -⟩
      obtain ⟨σe, hJ0, -, -, -, -, h80, -⟩ := hJ
      exact wcC_x1_lt _ σ0 (by rw [h80]; exact hm σe c0 hJ0)
    · exact Scc.Cert.Rt.A64.Print.code_field hp hend (by
        have h := SccCode.hello1_print
        simp only [Scc.Cert.Rt.A64.Print.printIn, Bool.and_eq_true, and_assoc] at h
        exact h.2.2.2.2.2.2.1)
        (by simp only [PrintA.N, PrintA.pcSvc, Scc.Cert.Rt.A64.Print.add4, Scc.Cert.Rt.A64.Print.add0])
    · rintro s c hAt k j c1 hlt ⟨σ0, c0, hJ, rfl, hP⟩
      have hk : k + j < printN (n σ0) (m σ0) := by
        rw [← hN σ0 c0 hJ, ← wcC_len (_root_.Executable.labels exe).label σ0]; exact hlt
      obtain ⟨_, _, -, -, -, -, -, -, hwn⟩ := id hP
      refine hpre _ _ _ _ _ (printC_load hd hP hk).toLocalRun (hpost _ _ _ _ _ (hlb σ0 c0 hJ F' s c hAt k j
        (by rw [hN σ0 c0 hJ]; exact hk)) ?_)
      rintro _ ⟨mw, b, rfl⟩
      obtain ⟨c2, r, hc2⟩ := printC_next (mw := mw) (b := b) hd hwn hk
      exact ⟨c2, r.toLocalRun, σ0, c0, hJ, rfl, hc2⟩
  · -- `hedge`: out of the loop, then the return
    intro σ0 c0 hJ c hP σ' hsl h0 h29 h30
    rw [hN σ0 c0 hJ] at hP
    obtain ⟨env, r⟩ := print_done_run (p := p) hP
    obtain ⟨c', r', hx⟩ := hret σ0 c0 hJ env σ' hsl h0 h29 h30
    exact ⟨c', r.toLocalRun.trans r', hx⟩

/-- `hello1_wcA_print_segW` with `hpre` and `hpost` from one closure fact
of the byte step (`LocalClosed`). -/
theorem hello1_wcA_print_segW' {W : Frag isaLSE2} {K : State → State → Prop}
    {BO : State → Nat → Ctl → (Ctl → Prop) → Prop} {WE : State → Ctl → Prop}
    {pw wm wn : AS → TermRun.Word} {n m : AS → Nat}
    (hp : Lays exe SccCode.hello1Prog) (hend : endPc = endOf exe SccCode.hello1Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi)
    {J0 : AS → Ctl → Prop} {x : ND} (ho : x.o = ⟨0, []⟩)
    (hW : WcAW W K exe endPc R F ms J0 (prC pw wn n m) (prC pw wn n m))
    (hlim : ∀ σ c, J0 σ c → LimOk ms F exe endPc (tcbA σ.regs 8) (σ.regs.SP.toBitVec - (96 : Int64).toBitVec))
    (hm : ∀ σ c, J0 σ c → σ.regs.X2.toBitVec.toNat * 8 < 2 ^ 63)
    (hra : ∀ σ c, J0 σ c → x.pc = Int64.ofBitVec σ.regs.X30.toBitVec)
    (hd : p.find? (·.name == "printL") = some printLD)
    (hN : ∀ σ0 c0, wcJ J0 σ0 c0 → wcLen σ0 = printN (n σ0) (m σ0))
    (hentry : ∀ σ c, wcJ J0 σ c → ∃ c1, LocalRun p c c1 ∧
      c1 = ⟨printBody, [("a", Hello1Src.sliceTy, [pw σ, wm σ, wn σ])], none⟩ ∧
      (wm σ).val = .num (m σ) ∧ m σ ≠ 0 ∧ (wn σ).val = .num (n σ))
    (hret : ∀ σ0 c0, wcJ J0 σ0 c0 → ∀ env,
      ∀ σ' : AS, (∀ k, -96 ≤ k → k < 0 → k % 8 = 0 → σ'.slot k = wcSl σ0 k) →
      σ'.regs.X0.toBitVec = 0#64 → σ'.regs.X29.toBitVec = σ0.slot (-16) → σ'.regs.X30.toBitVec = σ0.slot (-8) →
      ∃ c', LocalRun p ⟨.ret .unit, env, none⟩ c' ∧ x.J σ' c')
    (hE : PrintA.EmitW W K p lbl ms BO WE) (hK : ms.K = some Scc.Sem.A64.abi)
    (hcl : LocalClosed p BO)
    (hWs : ∀ (F' : MachineData → Prop) (σC : AS) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) σC .svc) s c → W s c ∧ ∀ s', ¬ K s s')
    (hlb : ∀ σ0 c0, wcJ J0 σ0 c0 → ∀ (F' : MachineData → Prop) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) (wcC (_root_.Executable.labels exe).label σ0) .svc) s c →
      ∀ k j, k + j < wcLen σ0 →
      BO s (((wcC (_root_.Executable.labels exe).label σ0).regs.X0.toBitVec + BitVec.ofNat 64 k).toNat + j)
        (loadC (pw σ0) (wn σ0) (m σ0) (k + j)) (fun c => ∃ mw b, c = nextC (pw σ0) (wn σ0) (m σ0) (k + j) mw b))
    (hwe : ∀ (F' : MachineData → Prop) (σC : AS) s c,
      At exe endPc (pR R) F' (pNA (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m)
        (prC pw wn n m) σC .svc) s c →
      ∀ k c1, pP (_root_.Executable.labels exe).label (wcJ J0) (prC pw wn n m) σC k c1 → WE s c1) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J0⟩)
      (fun s c => ∃ y, At exe endPc R F (aX (_root_.Executable.labels exe).label (wcJ J0)
        (prC pw wn n m) x y) s c) :=
  hello1_wcA_print_segW hp hend hF hR hal hlo hhi ho hW hlim hm hra hd hN hentry hret hE hK
    (fun s a c c' Φ r h => hcl s a c c' Φ Φ r h fun c1 h1 => ⟨c1, .refl c1, h1⟩)
    (fun s a c Φ Ψ h hΨ => hcl s a c c Φ Ψ (.refl c) h hΨ) hWs hlb hwe

end PrintAt

end Spike.Lib.A64.Flow.Hello1

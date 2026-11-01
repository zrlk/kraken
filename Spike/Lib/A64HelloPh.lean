/-
**hello.w's extended phase** (AArch64): the twin of
`Spike/Lib/A64WakePh.lean` at hello.w's listing (`SccCode.helloProg`,
canonical code base `0x210550`). The canonical phase index of hello.w's
certificate with the fifth bit of `Spike/Lib/A64PhExt.lean` set on the pcs
after the thread counter's add (`helloR`, `inR`, `phH`).

`helloR` is three code ranges named by helloProg's labels: the rest of
`scc_rt_thread_reserve` after its `ldaddal` (`.0_entry` + 6 up to
`scc_rt_thread_init`), `wc_main` (hello.w's `.L22_wc_main`) from the
reserve's return point `.sp3` up to `.stack_grow`, and the child stub
`.child13` up to `scc_rt_morestack`. Every fact is decided by
`decide +kernel` on the program's labels (through `codeT`, `codeT_eq`); no
pc range is a hypothesis. hello.w's pcs are wake.w's past `wc_waitLoop`
shifted (the reserve at `2165168`, wake's `2165132`).

- `RC`, `TC`, `SC`: the resolved ranges, the canonical phase table and the
  sites (`helloR_eq`, `phTab_eq`, `sites_eq`); `phH_eq`, `okPc_eq`.
- `ownH`: wake's `WakePh.ownW` (generic in the layout and the counter).
- `resPhH`: `ResPh` at `phH`, returning to `wc_main`'s `.sp3`.
- `phH_out`, `phH_in`: off `helloR` the canonical phase, in it plus `16`.
- `instOkH`: the instance's facts at `phH` with `ownH`.
-/
import Spike.Lib.A64WakePh
import Spike.Lib.A64HelloCode

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (PhRange PhTab inRs phOf phTabOf okPcOf sitesOf codeT codeT_eq blkOkN factOk)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64.PhExt (phExt)
open Spike.Lib.A64.Flow.Reserve
open Spike.Lib.A64.Rt.Reserve (ResPh ntA siPcs resPcs)
open Spike.Lib.A64.Rt.PhOfTab
open Spike.Lib.A64.Rt (ownUpdB InstOk RuntimeLayout)
open Spike.Lib.A64Consumer

/-- The canonical code base. -/
abbrev lo : Nat := 0x210550

/-! ## The ranges and the phase -/

/-- **The pcs after the thread counter's add**, by SccCode.helloProg's labels. -/
def helloR : List PhRange :=
  [⟨".L4_scc_rt_thread_reserve.0_entry", 6, "scc_rt_thread_init", 0⟩,
    ⟨".L22_wc_main.sp3", 0, ".L22_wc_main.stack_grow", 0⟩,
    ⟨".L22_wc_main.child13", 0, "scc_rt_morestack", 0⟩]

/-- The pc is in `helloR` (resolved in SccCode.helloProg at the canonical base). -/
def inR (pc : Nat) : Bool :=
  match helloR.mapM (PhRange.resolve (codeOf lo SccCode.helloProg)) with
  | some rs => inRs rs pc
  | none => false

/-- **hello.w's extended phase index.** -/
def phH : Nat → Nat := phExt (phOf lo SccCode.helloProg) inR

/-- The resolved ranges. -/
def RC : List (Nat × Nat) := [(2165208, 2165280), (2169696, 2169904), (2170008, 2170044)]

/-- The canonical phase table of SccCode.helloProg. -/
def TC : PhTab where
  p := [(2164048, 2164120), (2164748, 2164944)]
  l := [(2165680, 2165860)]
  n := [(2164048, 2164132), (2164748, 2165168), (2165280, 2165308), (2165436, 2165884)]
  t := [(2164048, 2164132), (2164748, 2165168), (2165280, 2165308), (2165436, 2165980)]

/-- The sites (`siteLabels` at `Link.abortName`). -/
def SC : List Nat := [2165976, 2166032, 2168296, 2168368, 2168440, 2168512, 2168584]

theorem helloR_eq : helloR.mapM (PhRange.resolve (codeOf lo SccCode.helloProg)) = some RC := by
  rw [← codeT_eq]; decide +kernel

theorem phTab_eq : phTabOf lo SccCode.helloProg = some TC := by
  unfold phTabOf; rw [← codeT_eq]; decide +kernel

theorem sites_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    sitesOf lo SccCode.helloProg Λ = some SC := by
  unfold sitesOf Scc.Cert.Rt.A64.sitesBy Scc.Cert.Rt.A64.siteLabels
  rw [hΛ, ← codeT_eq]; decide +kernel

/-- The phase through the resolved tables. -/
def phC (pc : Nat) : Nat := TC.ph pc + 16 * (inRs RC pc).toNat

/-- The off-site pcs through the resolved sites. -/
def okC (pc : Nat) : Bool := !(SC.contains pc)

theorem phH_eq : phH = phC := by
  funext pc
  unfold phH phExt phC phOf inR
  rw [phTab_eq, helloR_eq]

theorem inR_eq : inR = inRs RC := by
  funext pc; unfold inR; rw [helloR_eq]

/-- **Off `helloR` the extended phase is the canonical one.** -/
theorem phH_out {pc : Nat} (h : inRs RC pc = false) : phH pc = phOf lo SccCode.helloProg pc := by
  unfold phH phExt; rw [inR_eq, h, Bool.toNat_false, Nat.mul_zero, Nat.add_zero]

/-- **In `helloR` it is the canonical one plus `16`.** -/
theorem phH_in {pc : Nat} (h : inRs RC pc = true) : phH pc = phOf lo SccCode.helloProg pc + 16 := by
  unfold phH phExt; rw [inR_eq, h, Bool.toNat_true, Nat.mul_one]

theorem okPc_eq {Λ : Scc.Sem.Layout} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) :
    okPcOf lo SccCode.helloProg Λ = okC := by
  funext pc; unfold okPcOf okC; rw [sites_eq hΛ]

/-! ## The owned words -/

/-- **The owned words at an extended phase index**: wake's `ownW`
(`A64PhRec.ownOf`'s four counters and `scc_rt_nthreads` at `a` by the fifth
bit). -/
abbrev ownH (L : RuntimeLayout) (a : BitVec 64) (i : Nat) : List (Loc × Val) := Spike.Lib.A64.WakePh.ownW L a i

/-! ## `scc_rt_thread_reserve`'s phase facts -/

/-- The reserve's blocks' checks at `phH`, returning to `wc_main`'s `.sp3`. -/
theorem resBlks :
    blkOkN (codeT lo SccCode.helloProg) okC phC 2165168 0 rPro (some ".L22_wc_main.sp3") none = true ∧
    blkOkN (codeT lo SccCode.helloProg) okC phC 2165184 2 rArg (some ".L22_wc_main.sp3") none = true ∧
    blkOkN (codeT lo SccCode.helloProg) okC phC 2165184 6 rBnd (some ".L22_wc_main.sp3") none = true ∧
    blkOkN (codeT lo SccCode.helloProg) okC phC 2165184 15 rJ (some ".L22_wc_main.sp3") none = true ∧
    blkOkN (codeT lo SccCode.helloProg) okC phC 2165260 0 rRet (some ".L22_wc_main.sp3") none = true := by
  decide +kernel

/-- The reserve's labels. -/
theorem resLabs : codeOf lo SccCode.helloProg fnL = some 2165168 ∧ codeOf lo SccCode.helloProg entryL = some 2165184 ∧
    codeOf lo SccCode.helloProg okL = some 2165260 := by
  rw [← codeT_eq]; decide +kernel

/-- The reserve's single steps and the add off the sites, at `phH`. -/
theorem resSteps : factOk (codeT lo SccCode.helloProg) okC phC (.step entryL 0) = true ∧
    factOk (codeT lo SccCode.helloProg) okC phC (.step entryL 1) = true ∧
    factOk (codeT lo SccCode.helloProg) okC phC (.ok entryL 5) = true ∧ phC 2165204 = 0 ∧ phC 2165208 = 16 := by
  decide +kernel

variable {Λ : Scc.Sem.Layout} {lab : Label → Int64}

/-- `lab l + 4 k` at a resolved label. -/
theorem pc_eq (hlab : ∀ l a, codeOf lo SccCode.helloProg l = some a → lab l = Int64.ofNat a) {l : Label} {a : Nat}
    (hl : codeOf lo SccCode.helloProg l = some a) (k : Nat) :
    (lab l + Int64.ofNat (4 * k)).toBitVec.toNat = (a + 4 * k) % 2 ^ 64 := by
  rw [hlab l a hl, toNat_add]

/-- **`ResPh` at `phH`** with `ownH`, returning to `wc_main`'s `.sp3`, the
labels resolved as the certificate's (`hlab`), the counter off the four
counters (`hsep`); the take's field given. -/
theorem resPhH (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName) {L : RuntimeLayout} {Tk : State → Prop}
    (hlab : ∀ l a, codeOf lo SccCode.helloProg l = some a → lab l = Int64.ofNat a)
    (hsep : ntA lab ≠ L.pnA ∧ ntA lab ≠ L.lockA ∧ ntA lab ≠ L.freeNA ∧ ntA lab ≠ L.nextA)
    (noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s) :
    ResPh (okPcOf lo SccCode.helloProg Λ) phH Tk (ownH L (ntA lab)) lab (lab ".L22_wc_main.sp3") := by
  obtain ⟨bE, bA, bB, bJ, bO⟩ := resBlks
  obtain ⟨lF, lE, lO⟩ := resLabs
  obtain ⟨s0, s1, s5, p5, p6⟩ := resSteps
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at bE bA bB bJ bO
  rw [codeT_eq, ← okPc_eq hΛ, ← phH_eq] at s0 s1 s5
  rw [← phH_eq] at p5 p6
  have hn : ∀ {d : Nat → Bool} t, Scc.Cert.Rt.A64.deadN (codeOf lo SccCode.helloProg) none t = true → d t = true :=
    fun _ h => by simp [Scc.Cert.Rt.A64.deadN] at h
  have hr : ∀ r, some ".L22_wc_main.sp3" = some r → lab ".L22_wc_main.sp3" = lab r := fun _ h => by cases h; rfl
  have hrmw : (rmwPc lab).toBitVec.toNat = 2165204 := pc_eq hlab lE 5
  have hrmw4 : (rmwPc lab + Int64.ofNat 4).toBitVec.toNat = 2165208 := by
    unfold rmwPc; rw [hlab _ _ lE, Int64.add_assoc, ← Int64.ofNat_add, toNat_add]
  exact {
    e := blkPh_of_blkOkN hlab lF hr hn bE
    arg := blkPh_of_blkOkN hlab lE hr hn bA
    bnd := blkPh_of_blkOkN hlab lE hr hn bB
    j := blkPh_of_blkOkN hlab lE hr hn bJ
    ok := blkPh_of_blkOkN hlab lO hr hn bO
    si := by
      intro p hp
      simp only [siPcs, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact step_of_factOk hlab s0
      · exact step_of_factOk hlab s1
    rmwOk := ok_of_factOk hlab s5
    noTk := noTk
    rmwIn := ⟨(0#64).setWidth 128, by rw [hrmw, p5]; simp [ownH, Spike.Lib.A64.WakePh.ownW]⟩
    rmwUpd := by
      obtain ⟨h1, h2, h3, h4⟩ := hsep
      rw [hrmw, hrmw4, p5, p6]
      simp [ownUpdB, ownH, Spike.Lib.A64.WakePh.ownW, Spike.Lib.A64.PhRec.ownOf, Ne.symm h1, Ne.symm h2,
        Ne.symm h3, Ne.symm h4]
      decide }

/-! ## The instance's facts -/

/-- **The instance's facts at `phH`** with `ownH` (the counter at `a`) and
a take's phase `TkH` of the phase index, for a layout of SccCode.helloProg at the
canonical base, the take site at its label (`hsite`). -/
theorem instOkH {L : RuntimeLayout} (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo) (a : BitVec 64)
    (TkH : Nat → Prop) {rS : Scc.Sem.Range}
    (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
      some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s)))
      (fun s => TkH (phH (pcOf s))) (Spike.Lib.A64.PhRec.K L rS) (okPcOf lo SccCode.helloProg L.Λ) phH L.pfx where
  lays := L.lays
  endOk := rfl
  labOk := rfl
  same := fun _ _ h => ⟨congrArg (ownH L a) h, by simp only [h]⟩
  off := by
    have h := Spike.Lib.A64.PhRec.off L (rS := rS) hsite
    unfold Spike.Lib.A64.PhRec.okPc at h
    rw [hp, hlo] at h
    exact h

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.resPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.resPhH

/-- info: 'Spike.Lib.A64.HelloPh.instOkH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.instOkH

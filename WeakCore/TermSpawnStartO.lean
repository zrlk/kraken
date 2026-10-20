import WeakCore.TermSpawnFinal
import WeakCore.TermSpawnKidMem
/-!
# TermSpawnStartO — `SysInvO` after the barrier-spawn reshape

Closes the named hypothesis `hO` of `startOKX_spawnS`.

`spawnS` is not a sequence of mid-run `spawnT` steps (it ends the setup thread `0` and replaces it
by the kids), so `ownLive_spawnT`/`obsAll_spawnT` do not apply literally; the kids-config
facts are: `ObsAll` = `TermSpawnKidMem.obsAll_kid` (memory/pairs kept, `1 ≤ kids.length`),
`OwnLive` = `ownLive_grow` (owners below the old size `1`).

The `SysInvN` part and the setup-end witnesses come from `spawnS_sysInvN_witness` (TermSpawnFinal),
shared with `startOK_spawnS_proved`.
-/
namespace TermSpawn
open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys TermMain
open WeakMem (Msg Memory Address VState Ts Arch AllocLabel)
open TermSpawnSim

/-- Ghost owners stay live when the thread array does not shrink (any `fpOf`). -/
theorem ownLive_grow {Eg : GEnv} {c c' : Cfg} (F : Nat → List Ts) (h : OwnLive Eg c)
    (hsz : c.ths.size ≤ c'.ths.size) : OwnLive { Eg with fpOf := F } c' :=
  ⟨fun l cl i hs ho => Nat.lt_of_lt_of_le (h.1 l cl i hs ho) hsz,
    fun l B hB => Nat.lt_of_lt_of_le (h.2 l B hB) hsz⟩

/-- **`SysInvO` after the spawn reshape** (closes the `hO`). -/
theorem sysInvO_spawnS_proved {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res}
    {cpre cs : Cfg} {th0 th : TTh} {f : String} {ts : List Ty} {d : Decl} {a : At} {rt : Ty} {res : List Word}
    {kids : List Kid}
    (O0 : ObligationsF p k arch Init (fun _ => True) (phant (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) cpre))
    (hk : k.storeDepRts = true)
    (h0 : InitOK p k arch Init (fun _ => True) cpre) (h1 : cpre.ths.size = 1)
    (hpre : cpre.ths[0]? = some th0) (hset : th0.term = .tail f [] (.var "a") ts) (hstk0 : th0.stack = [])
    (hd : p.find f = .ok d)
    (hR0 : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).wf 0 0 = true)
    (hR0a : (substTs ts.reverse 0 0 (instT [] 0 d.retTy)).arrFree = true)
    (hR0w : TermScope.argOK (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) = true)
    (hrun : TermStep.Steps p k arch cpre cs) (hnp : AllNoProm cs)
    (hth : cs.ths[0]? = some th) (hret : th.term = .ret a) (hstk : th.stack = [])
    (hev : evalAt th.env a = some (rt, res))
    (hkids : kids ≠ []) (hok : ∀ kd ∈ kids, KidOK p (substTs ts.reverse 0 0 (instT [] 0 d.retTy)) kd) :
    SysInvO p k arch Init (fun _ => True) (spawnS cs res kids) := by
  obtain ⟨Eg, Tot, HP, HS, H, hOL, hOb⟩ :=
    spawnS_sysInvN_witness O0 hk h0 h1 hpre hset hstk0 hd hR0 hR0a hR0w hrun hnp hth hret hstk hev hkids hok
  have hsz : cs.ths.size ≤ (spawnS cs res kids).ths.size := by
    rw [spawnS_size hth, (steps_size hrun).trans h1]; exact List.length_pos_iff.2 hkids
  exact ⟨EgS Eg, _, _, _, _, _, H, ownLive_grow (fun _ => []) hOL hsz,
    TermSpawnKidMem.obsAll_kid (fun _ => []) hOb (spawnS_mem hth) (spawnS_pairs hth) hsz⟩

end TermSpawn

#print axioms TermSpawn.sysInvO_spawnS_proved

/-! (hygiene) axiom reports for theorems that had none. -/
#print axioms TermSpawn.ownLive_grow

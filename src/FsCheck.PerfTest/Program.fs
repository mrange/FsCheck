module Tries =
  open System.Diagnostics
  open System.Text

  type CharTrie<'T> =                                             // ' Buggy F# sublime plugin...
    | CharTrie0 of 'T option                                      // ' Buggy F# sublime plugin...
    | CharTrieP of 'T option*string*CharTrie<'T>
    | CharTrie1 of 'T option*char*CharTrie<'T>
    | CharTrie2 of 'T option*char*CharTrie<'T>*char*CharTrie<'T>  // ' Buggy F# sublime plugin...
    | CharTrieN of 'T option*Map<char, CharTrie<'T>>

    member inline x.IsEmpty =
      match x with
      | CharTrie0 _ ->
        true
      | _ ->
        false

    member x.CheckInvariant () =
      match x with
      | CharTrie0 _ ->
        true
      | CharTrieP (_,cs0,nt0) ->
        cs0 <> null
        && cs0.Length > 1
        && nt0.CheckInvariant ()
      | CharTrie1 (_,_,nt0) ->
        nt0.CheckInvariant ()
      | CharTrie2 (_, c0, nt0, c1, nt1) ->
        c0 <> c1
        && nt0.CheckInvariant ()
        && nt1.CheckInvariant ()
      | CharTrieN (_, m) ->
        // Map guarantees all keys unique
        m
        |> Map.forall (fun _ nt -> nt.CheckInvariant ())

  [<GeneralizableValue>]
  let Empty     = CharTrie0 None

  let inline IsEmpty (ct : CharTrie<'T>) = ct.IsEmpty

  let inline (|MatchEmpty|MatchNonEmpty|) (ct : CharTrie<'T>) =
    if ct.IsEmpty then
      MatchEmpty
    else
      MatchNonEmpty

  module Details =
    let inline Scan (s : string) (b : int) (cs : string) : int =
      let e = min s.Length (b + cs.Length)

      let rec impl i =
        if i < e then
          let sc  = s.[i]
          let csc = cs.[i - b]
          if sc = csc then impl (i + 1)
          else i
        else
          i

      impl b

    let rec MatchImpl (p : string) bi bm i l t =
      let inline foundnm n m ov  =
        match ov with
        | Some _ -> n, m, ov
        | _ -> bi, m, bm
      let inline foundn n ov  =
        foundnm n i ov
      let inline found ov  =
        foundn i ov
      let inline nextn n ov nt =
        match ov with
        | Some _ ->
          MatchImpl p i ov n l nt
        | _ ->
          MatchImpl p bi bm n l nt
      let inline next ov nt =
        nextn (i + 1) ov nt

      if i < l then
        let c = p.[i]
        match t with
        | CharTrie0 ov ->
          found ov
        | CharTrieP (ov,cs0,nt0) ->
          let ni = Scan p i cs0
          if ni < i + cs0.Length then
            foundn ni ov
          else
            nextn ni ov nt0
        | CharTrie1 (ov,c0,nt0) ->
          if c = c0 then
            next ov nt0
          else
            found ov
        | CharTrie2 (ov,c0,nt0,c1,nt1) ->
          if c = c0 then
            next ov nt0
          elif c = c1 then
            next ov nt1
          else
          found ov
        | CharTrieN (ov, m) ->
          match Map.tryFind c m with
          | None    ->
            found ov
          | Some nt ->
            next ov nt
      else
        match t with
        | CharTrie0 ov
        | CharTrieP (ov,_,_)
        | CharTrie1 (ov,_,_)
        | CharTrie2 (ov,_,_,_,_)
        | CharTrieN (ov, _) ->
          found ov

    let rec UpdateImpl (k : string) ov i t =
      let inline nextn n t =
        UpdateImpl k ov n t
      let inline next t =
        nextn (i + 1) t

      if i < k.Length then
        let c = k.[i]
        match t with
        | CharTrie0 pov when i + 1 = k.Length ->
          CharTrie1 (pov, c, next Empty)
        | CharTrie0 pov ->
          CharTrieP (pov, k.Substring i, nextn k.Length Empty)
        | CharTrieP (pov,cs0,nt0) ->
          let si                = Scan k i cs0
          let nsi               = si + 1
          let sci               = si - i
          let nsci              = sci + 1
          let inline leftn i tov t =
            match i with
            | 0 when Option.isSome tov ->
              failwith "leftn: invalid case: 0"
            | 0 ->
              t
            | 1 ->
              CharTrie1 (tov, cs0.[0], t)
            | _ ->
              CharTrieP (tov, cs0.Substring (0, i), t)
          let inline left tov t =
            leftn sci tov t
          let inline rightn i tov t =
            let rem = cs0.Length - i
            match rem with
            | 0 when Option.isSome tov ->
              failwith "rightn: invalid case: 0"
            | 0 ->
              t
            | 1 ->
              CharTrie1 (tov, cs0.[i], t)
            | _ ->
              CharTrieP (tov, cs0.Substring i, t)
          let inline right tov t =
            rightn sci tov t
          let inline junction tov=
            CharTrie2 (
              tov       ,
              cs0.[sci] , rightn (sci + 1) None nt0,
              k.[si]    , UpdateImpl k ov nsi Empty
              )

          if sci = cs0.Length then  // false ==> sci < cs0.Length
            // k: "abcde", t: "abcde" ==>
            //  CharTrieP (pov, "abcde", CharTrie0 ov)
            CharTrieP (pov, cs0, nextn si nt0)
          elif si = k.Length then
            // k: "ab", t: "abcde" ==>
            //  CharTrieP (pov, "ab", CharTrieP (ov, "cd", next))
            left pov (right ov nt0)
          elif sci = 0 then
            // k: "b", t: "abcde" ==>
            //  CharTrie2 (pov, 'a', CharTrieP (None, "bcde", next), 'b', CharTrie0 ov)
            junction pov
          else
            // k: "abd", t: "abcde" ==>
            //  CharTrieP (pov, "ab", CharTrie2 (None, 'c', CharTrieP (None, "de", next), 'd', CharTrie0 ov))
            left pov (junction None)
        | CharTrie1 (pov, c0, nt0) when c = c0 ->
          CharTrie1 (pov, c0, next nt0)
        | CharTrie1 (pov, c0, nt0) ->
          CharTrie2 (pov, c0, nt0, c, next Empty)
        | CharTrie2 (pov, c0, nt0, c1, nt1) when c = c0 ->
          CharTrie2 (pov, c0, next nt0, c1, nt1)
        | CharTrie2 (pov, c0, nt0, c1, nt1) when c = c1 ->
          CharTrie2 (pov, c0, nt0, c1, next nt1)
        | CharTrie2 (pov, c0, nt0, c1, nt1) ->
          CharTrieN (pov, Map.empty |> Map.add c0 nt0 |> Map.add c1 nt1 |> Map.add c (next Empty))
        | CharTrieN (pov, m) ->
          match Map.tryFind c m with
          | None    ->
            CharTrieN (pov, m |> Map.add c (next Empty))
          | Some nt ->
            CharTrieN (pov, m |> Map.remove c |> Map.add c (next nt))
      else
        match t with
        | CharTrie0 _ ->
          CharTrie0 ov
        | CharTrieP (_, cs0, nt0) ->
          CharTrieP (ov, cs0, nt0)
        | CharTrie1 (_, c0, nt0) ->
          CharTrie1 (ov, c0, nt0)
        | CharTrie2 (_, c0, nt0, c1, nt1) ->
          CharTrie2 (ov, c0, nt0, c1, nt1)
        | CharTrieN (_, m) ->
          CharTrieN (ov, m)

    let rec TrimImpl t =
      match t with
      | CharTrie0 _ -> t
      | CharTrieP (pov, cs0, nt0) ->
        // TODO: Implement trim to and from CharTrieP
        CharTrieP (pov, cs0, nt0)
      | CharTrie1 (pov, c0, nt0) ->
        match TrimImpl nt0 with
        | MatchEmpty ->
          CharTrie0 pov
        | tnt0 ->
          CharTrie1 (pov, c0, tnt0)
      | CharTrie2 (pov, c0, nt0, c1, nt1) ->
        match TrimImpl nt0, TrimImpl nt1 with
        | MatchEmpty, MatchEmpty ->
          CharTrie0 pov
        | tnt0, MatchEmpty ->
          CharTrie1 (pov, c0, tnt0)
        | MatchEmpty, tnt1 ->
          CharTrie1 (pov, c1, tnt1)
        | tnt0, tnt1 ->
          CharTrie2 (pov, c0, tnt0, c1, tnt1)
      | CharTrieN (pov, m) ->
        let nm =
          m
          |> Map.map (fun _ nt -> TrimImpl nt)
          |> Map.filter (fun _ nt -> not (IsEmpty nt))
        match nm with
        | _ when nm.Count = 0 ->
          CharTrie0 pov
        | _ when nm.Count = 1 ->
          let kv0 = nm |> Seq.head
          CharTrie1 (pov, kv0.Key, kv0.Value)
        | _ when nm.Count = 2 ->
          let [|kv0; kv1|] = nm |> Seq.take 2 |> Seq.toArray
          CharTrie2 (pov, kv0.Key, kv0.Value, kv1.Key, kv1.Value)
        | _ ->
          CharTrieN (pov, nm)

    let rec AllImpl (sb : StringBuilder) (ra : ResizeArray<string*'T>) t =
      // TODO: Not tail recursive
      let inline emit ov =
        match ov with
        | Some v ->
          ignore <| ra.Add (sb.ToString (), v)
        | _ ->
          ()

      let inline nextn (cs : string) nt =
        ignore <| sb.Append cs
        AllImpl sb ra nt
        ignore <| sb.Remove (sb.Length - cs.Length, cs.Length)

      let inline next (c : char) nt =
        ignore <| sb.Append c
        AllImpl sb ra nt
        ignore <| sb.Remove (sb.Length - 1, 1)

      match t with
      | CharTrie0 ov ->
        emit ov
      | CharTrieP (ov, cs0, nt0) ->
        emit ov
        nextn cs0 nt0
      | CharTrie1 (ov, c0, nt0) ->
        emit ov
        next c0 nt0
      | CharTrie2 (ov, c0, nt0, c1, nt1) ->
        emit ov
        next c0 nt0
        next c1 nt1
      | CharTrieN (ov, m) ->
        emit ov
        m |> Map.iter next

  let MatchAt (p : string) (at : int) (ct : CharTrie<'T>) : int*int*'T option =
    Details.MatchImpl p -1 None at p.Length ct

  let Match (p : string) (ct : CharTrie<'T>) : int*int*'T option =
    Details.MatchImpl p -1 None 0 p.Length ct

  let Update (k : string) (ov : 'T option) (ct : CharTrie<'T>) : CharTrie<'T> =
    Details.UpdateImpl k ov 0 ct

  let Trim (ct : CharTrie<'T>) : CharTrie<'T> =
    Details.TrimImpl ct

  let All (ct : CharTrie<'T>) : (string*'T) [] =
    let sb = StringBuilder 16
    let ra = ResizeArray<string*'T> ()  // ' Buggy F# sublime plugin...
    Details.AllImpl sb ra ct
    ra.ToArray ()

open FsCheck
open Microsoft.FSharp.Core.Printf
open System
open System.Diagnostics
open System.IO
open Tries

type TrieProperties() =
  static let nonNull k = if String.IsNullOrEmpty k then "" else k

  static let precheck (ct : CharTrie<int>) =
    ct.CheckInvariant ()

(*
  Busted currently
  static member ``has value after insert`` k ct (v : int) =
    precheck ct ==> fun () ->
      let k   = nonNull k
      let nct = Update k (Some v) ct
      let m   = Match k nct
      match m with
      | i, ii, Some iv when i = k.Length && ii = k.Length && iv = v->
        nct.CheckInvariant ()
      | _ ->
        false
*)

  static member ``find parent value when looking for descendent`` k ct (v : int) dk =
    precheck ct ==> fun () ->
      let k   = nonNull k
      let dk  = nonNull dk
      let fk  = k + dk
      dk.Length > 0 ==> fun () ->
        let m  = Match fk ct
        let fullMatch =
          match m with
          | i, _, Some _ when i = fk.Length -> true
          | _ -> false
        not fullMatch ==> fun () ->
          let nct = Update k (Some v) ct
          let dm  = Match fk nct
          match dm with
          | i, ii, Some iv when i = k.Length && ii < fk.Length && iv = v->
            nct.CheckInvariant ()
          | _ ->
            false

  static member ``lacks value after remove`` k ct =
    precheck ct ==> fun () ->
      let k   = nonNull k
      let nct = Update k None ct
      let m   = Match k nct
      match m with
      | i, ii, None when i <= k.Length && ii <= k.Length ->
        nct.CheckInvariant ()
      | i, ii, Some _ when i < k.Length && ii <= k.Length ->  // This case matches if there's a match higher up in the trie
        nct.CheckInvariant ()
      | _ ->
        false

  static member ``All has value after insert`` k ct (v : int) =
    precheck ct ==> fun () ->
      let k   = nonNull k
      let nct = Update k (Some v) ct
      let a   = All nct
      match a |> Array.tryFind (fun (kk,_) -> kk = k) with
      | Some (ak, av) when ak = k && v = av ->
        nct.CheckInvariant ()
      | _ ->
        false

  static member ``All lacks value after remove`` k ct =
    precheck ct ==> fun () ->
      let k   = nonNull k
      let nct = Update k None ct
      let a   = All nct
      match a |> Array.tryFind (fun (kk,_) -> kk = k) with
      | Some (_, _) ->
        true
      | _ ->
        nct.CheckInvariant ()

  static member ``trim does not change content`` ct =
    precheck ct ==> fun () ->
      let p   = All ct
      let nct = Trim ct
      let a   = All ct
      p = a && nct.CheckInvariant ()

let errors = ref 0

let colorprint cc (msg : string) =
  let occ = Console.ForegroundColor
  try
    Console.ForegroundColor <- cc
    Console.WriteLine msg
  finally
    Console.ForegroundColor <- occ

let colorprintf cc format =
  ksprintf (colorprint cc) format

let success   msg = colorprintf ConsoleColor.Green    "SUCCESS: %s" msg
let hilight   msg = colorprintf ConsoleColor.White    "HILIGHT: %s" msg
let info      msg = colorprintf ConsoleColor.DarkGray "INFO   : %s" msg
let warning   msg = colorprintf ConsoleColor.Yellow   "WARNING: %s" msg
let error     msg =
  incr errors
  colorprintf ConsoleColor.Red "ERROR  : %s" msg

let successf  fmt = ksprintf success  fmt
let hilightf  fmt = ksprintf hilight  fmt
let infof     fmt = ksprintf info     fmt
let warningf  fmt = ksprintf warning  fmt
let errorf    fmt = ksprintf error    fmt

let timeIt (a : unit -> 'T) : int64*'T =
  let sw = Stopwatch ()

  sw.Start ()
  let r = a ()
  sw.Stop ()

  sw.ElapsedMilliseconds, r

let testTrieProperties () =
  let runner =
    { new IRunner with
      member __.OnStartFixture t =
        hilight (Runner.onStartFixtureToString t)
      member __.OnArguments (ntest, args, every) =
        // info (every ntest args)
        ()
      member __.OnShrink(args, everyShrink) =
        // warning (everyShrink args)
        ()
      member __.OnFinished(name,testResult) =
        let isTrue = match testResult with | TestResult.True _ -> true | _ -> false
        if isTrue then
          success (Runner.onFinishedToString name testResult)
        else
          error (Runner.onFinishedToString name testResult)
    }

  let config =
    {
      Config.Quick with
        MaxTest = 1000
        Runner  = runner
    }

  let ms, _ = timeIt <| fun () -> Check.All<TrieProperties> config

  hilightf "Checking TrieProperties took: %d ms" ms

[<EntryPoint>]
let main argv =
  try
    testTrieProperties  ()
  with
    | e -> errorf "Exception (%s): %A" (e.GetType().Name) e.Message

  if !errors > 0 then
    errorf "Test failures detected: %d" !errors
    999
  else
    successf "No failures detected"
    0


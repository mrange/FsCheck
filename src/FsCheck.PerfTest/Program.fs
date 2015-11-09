open FsCheck
open Microsoft.FSharp.Core.Printf
open System
open System.Diagnostics
open System.IO

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

type MyClass(n : int) =
  let x = n + 1

let testCtorPerf () =
  let generator = Arb.from<MyClass>.Generator

  let ms, _ = timeIt <| fun () -> 
    for i in 0..1000 do
      generator |> Gen.sample 100 2000 |> ignore

  hilightf "Checking CtorPerf took: %d ms" ms

[<EntryPoint>]
let main argv =
  try
    testCtorPerf  ()
  with
    | e -> errorf "Exception (%s): %A" (e.GetType().Name) e.Message

  if !errors > 0 then
    errorf "Test failures detected: %d" !errors
    999
  else
    successf "No failures detected"
    0


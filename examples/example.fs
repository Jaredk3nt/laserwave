namespace Example

open System
open System.IO

module Option =
  let ofEmpty (str: string) =
    if String.IsNullOrEmpty str then None else Some str

module Util =
  let flip f a b = f b a
  let joinPath a b = Path.Combine(a, b)

  let getEnv a =
    Option.ofEmpty
    <| Environment.GetEnvironmentVariable a

module Program =
  open Util

  let mapping = flip joinPath ".config\\"

  let fallback =
    Environment.GetEnvironmentVariable "USERPROFILE"
    |> Option.ofEmpty
    |> Option.map (flip joinPath ".config\\")

  let configDir =
    List.pick id
    <| [ getEnv "One"
         getEnv "Two"
         getEnv "Three" |> Option.map mapping
         getEnv "Four" |> Option.map mapping
         fallback ]

  [<EntryPoint>]
  let main argv =
    printfn "config: %s" configDir
    0 // return an integer exit code

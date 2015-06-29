(*** hide ***)
#load "packages/FsLab/FsLab.fsx"
(**
Probability DSL
==

Being inspired by excellent probmod.org, I have decided to take a look at F# implementation of similar generative sampler.

Let's start with most basic distribution sampler:

**)

let uniform = 
    let rand = new System.Random()
    rand.NextDouble

let binomial p = p > uniform()

(**
Let's test it with simple sampling query:
**)

let binProb = 0.5

let samples = Seq.initInfinite (fun _ -> binomial binProb)

Seq.take 10 samples |> Seq.toList

(**
As expected, this gives us 10 samples of fair coin tosses.

Let's define simple query

**)

let query1 = Seq.initInfinite (fun _ -> let a = binomial binProb
                                        let b = binomial binProb
                                        if a && b then "BothTrue"
                                        else "None")

let histogram data =
    data |> Seq.countBy id |> Seq.sortBy fst |> Seq.toList

Seq.take 100 query1 |> histogram

(**
Now we can simulate 100 samples of 2 coin tosses and show probability distribution approximation where both coins are heads (or true as in above case).

Let's try to infer (through sampling) the fairness of an observed coin:
**)

type Coin =
    | Heads
    | Tails

let observation2 = [ Heads; Heads; Tails; Heads; Heads; Heads; Tails; Heads; Heads; Heads; Heads; Tails]

let query2 observation = Seq.initInfinite (fun _ -> let probPrior = uniform()
                                                    let generated = List.init (List.length observation) (fun _ -> if binomial probPrior then Heads else Tails)
                                                    if generated = observation then Some probPrior
                                                    else None)

let result2 =
    let res = (query2 observation2) |> Seq.filter Option.isSome |> Seq.take 100 |> Seq.toList
    let avg = Seq.averageBy (fun (v: float option) -> v.Value) res
    (avg, res)

(**
Not things are getting a bit more interesting. We are able to infer, through simulation, how likely the coin will land heads. (posterior of $theta$ parameter of binomial distribution given the observed data and prior belief that coin was fair)

priorProb is our prior belief that coin is fair.

Let's separate query from iteration and utilise "rQuery" rejection query workflow.
**)

type RejectionQueryBuilder() =
    member x.Bind(v,f) = Option.bind f v
    member x.Return v = Some v
    member x.Zero () = None
    
let rQuery = RejectionQueryBuilder()

let observation3 = [ Heads; Heads; Tails; Heads; Heads; Heads; Tails; Heads; Heads; Heads; Heads; Tails]

let repeat f = Seq.initInfinite (fun _ -> f())

let query3 observation = 
        rQuery { let probPrior = uniform()
                 let coinFlip = fun _ -> if binomial probPrior then Heads else Tails
                 let generated = List.init (List.length observation) coinFlip
                 if generated = observation then return probPrior}

let evaluate3 =
    let res = repeat (fun () -> query3 observation3) 
                |> Seq.filter Option.isSome
                |> Seq.take 100
                |> Seq.toList
    let avg = Seq.averageBy (fun (v: float option) -> v.Value) res
    (avg, res)

(**
Let's have a look at more complicated reasoning (Tug of War) examples:
**)
open MathNet.Numerics.Distributions

let gaussian mean stddev =
    Normal(mean, stddev).Sample()

let memoise f =
    let dict = new System.Collections.Generic.Dictionary<_,_>()
    (fun k ->
        if dict.ContainsKey k then dict.[k]
        else
            let result = f(k)
            dict.Add (k, result)
            result)

type Teams =
    | Team1
    | Team2

let query4 () =
    rQuery { let strengthOf = memoise (fun _ -> gaussian 0. 1.)
             let isLazy person = binomial (1./3.)
             let personPullingPower person = if isLazy person then (strengthOf person) / 2.
                                             else strengthOf person
             let teamPullingPower = Seq.sumBy personPullingPower
             let winner team1 team2 =
                if (teamPullingPower team1) > (teamPullingPower team2) then Team1
                else Team2
             if (winner ["bob"; "mary"] ["tom"; "sue"]) = Team1 &&
                (winner ["bob"; "sue"] ["tom"; "jim"])  = Team1 then return (strengthOf "bob") }

let evaluate4 =
    let res = repeat query4 
                |> Seq.filter Option.isSome
                |> Seq.take 1000
                |> Seq.toList
    let avg = Seq.averageBy (fun (v: float option) -> v.Value) res
    (res, avg)

let query5 () =
    rQuery { let strengthOf = memoise (fun _ -> gaussian 0. 1.)
             let isLazy person = binomial (1./3.)
             let personPullingPower person = if isLazy person then (strengthOf person) / 2.
                                             else strengthOf person
             let teamPullingPower = Seq.sumBy personPullingPower
             let winner team1 team2 =
                if (teamPullingPower team1) > (teamPullingPower team2) then Team1
                else Team2
             if (strengthOf "mary") >= (strengthOf "sue") &&
                (winner ["bob";"francis"] ["tom";"jim"]) = Team1 then return (winner ["bob";"mary"] ["jim";"sue"]) = Team1 }

let evaluate5 =
    let n = 1000
    let res = repeat query5 
                |> Seq.filter Option.isSome
                |> Seq.take n
                |> Seq.toList
    let hist = Seq.map (fun (v: bool option) -> v.Value) res
              |> histogram
    (res, hist)

let evaluate n q =
    repeat q |> Seq.filter Option.isSome
             |> Seq.take n
             |> Seq.map Option.get

evaluate 100 (fun () -> query3 observation3) |> Seq.average
evaluate 100 query4 |> Seq.average
evaluate 100 query5 |> histogram
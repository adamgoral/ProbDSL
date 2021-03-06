(*** hide ***)
#load "packages/FsLab/FsLab.fsx"
(**
Probability DSL
==

Being inspired by excellent probmod.org, I have decided to take a look at F# implementation of similar generative sampler.

Let's start with most basic distribution sampler:

*)

let uniform = 
    let rand = new System.Random()
    rand.NextDouble

let binomial p = p > uniform()

(**
Let's test it with simple sampling query:
*)

let binProb = 0.5

let samples = Seq.initInfinite (fun _ -> binomial binProb)

(*** define-output:uniformSample ***)
Seq.take 10 samples |> Seq.toList
(*** include-it:uniformSample ***)

(**
This gives us 10 samples of fair coin tosses.

Let's define simple query

*)

let query1 = Seq.initInfinite (fun _ -> let a = binomial binProb
                                        let b = binomial binProb
                                        if a && b then "BothTrue"
                                        else "None")

let histogram data =
    data |> Seq.countBy id |> Seq.sortBy fst |> Seq.toList

(**
Now we can simulate 100 samples of 2 coin tosses and show probability distribution approximation where both coins are heads (or true as in above case).
*)

(*** define-output:bothCoins ***)
let q1result = Seq.take 100 query1 |> histogram
open FSharp.Charting
Chart.Column q1result
(*** include-it:bothCoins ***)

(**
As expected, the probability of both fair coins being true (heads) is 25%.

Let's try to infer (through sampling) the fairness of an observed coin:
*)

type Coin =
    | Heads
    | Tails

let observation2 = [ Heads; Heads; Tails; Heads; Heads; Heads; Tails; Heads; Heads; Heads; Heads; Tails]

let query2 observation = Seq.initInfinite (fun _ -> let probPrior = uniform()
                                                    let generated = List.init (List.length observation) (fun _ -> if binomial probPrior then Heads else Tails)
                                                    if generated = observation then Some probPrior
                                                    else None)

(*** define-output:q2result ***)
(query2 observation2) 
    |> Seq.filter Option.isSome 
    |> Seq.take 100 
    |> Seq.averageBy (fun (v: float option) -> v.Value)
(*** include-it:q2result ***)

(**
Now things are getting a bit more interesting. We are able to infer, through simulation, how likely the coin will land heads. (posterior of $theta$ parameter of binomial distribution given the observed data and prior belief that coin was fair)

priorProb is our prior belief that coin is fair.

Query definitions are starting to become a bit messy. Let's separate query from iteration and utilise "rQuery" rejection query workflow.
*)

type RejectionQueryBuilder() =
    member x.Bind(v,f) = Option.bind f v
    member x.Return v = Some v
    member x.Zero () = None

// Basic computation workflow    
let rQuery = RejectionQueryBuilder()

let observation3 = [ Heads; Heads; Tails; Heads; Heads; Heads; Tails; Heads; Heads; Heads; Heads; Tails]

let repeat f = Seq.initInfinite (fun _ -> f())

let query3 observation = 
        rQuery { let probPrior = uniform()
                 let coinFlip = fun _ -> if binomial probPrior then Heads else Tails
                 let generated = List.init (List.length observation) coinFlip
                 // inefficient check
                 if generated = observation then return probPrior}

(**
This time let's use evaluate helper function*)
let evaluate n q =
    repeat q |> Seq.filter Option.isSome
             |> Seq.take n
             |> Seq.map Option.get

(*** define-output:q3Result ***)
evaluate 100 (fun () -> query3 observation3) |> Seq.average
(*** include-it:q3Result ***)
(**
Now we have generic query workflow and repeat function that can be used to define quite basic sampling.

Matching of generated sequence with observation is very inefficient.
 As the length of observed sequence grows, the algorithm will become increasingly slow as it will become more unlikely to generate sequence matching observations.
 I will demonstrate more efficient ways of doing this in Part2.

Meantime let's have a look at more complicated (and more fun) reasoning (Tug of War) examples:
*)
open MathNet.Numerics.Distributions

let gaussian mean stddev =
    Normal(mean, stddev).Sample()

// helper function to allow us remember a value once it has been calculated once
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

(**We are insterested in estimating Bob's relative strength, given observed winning teams for 2 trials.*)
let query4 () =
    rQuery { // generate random value for person's strength and memorise as the person strenght will not change from trial to trial
             let strengthOf = memoise (fun _ -> gaussian 0. 1.)
             // generate indicator for each trial whenever given person is lazy during that trial
             let isLazy person = binomial (1./3.)
             let personPullingPower person = if isLazy person then (strengthOf person) / 2.
                                             else strengthOf person
             let teamPullingPower = Seq.sumBy personPullingPower
             let winner team1 team2 =
                if (teamPullingPower team1) > (teamPullingPower team2) then Team1
                else Team2
             if (winner ["bob"; "mary"] ["tom"; "sue"]) = Team1 &&
                (winner ["bob"; "sue"] ["tom"; "jim"])  = Team1 then return (strengthOf "bob") }

(*** define-output:q4Result ***)
evaluate 100 query4 |> Seq.average
(*** include-it:q4Result ***)

(**Similar to previous we are instersting in knowing probability if Bob and Mary will win given mary is stronger than sue and Bob and Francis have won in previous trial*)
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

(*** define-output:q5Result ***)
evaluate 1000 query5 |> histogram |> Chart.Column
(*** include-it:q5Result ***)

(**
According to above (unnormalised) chart, Team1 (Bob and Mary) is most likely to win.*)
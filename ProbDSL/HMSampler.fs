namespace ProbDSL
module HMSampler =
    open System
    open MathNet.Numerics.Distributions
    open MathNet.Numerics.LinearAlgebra

    type Sample =
        | Real of float
        | Bool of bool
        | Integer of int
        | Vec of Vector<float>
        | Mat of Matrix<float>

    type DistributionType =
        | DTBeta of float * float
        | DTBernoulli of float
        | DTDiscrete of int * int
        | DTGaussian of float * float
        | DTGamma of float * float
        | DTUniform of float * float
        | DTGaussianMultivariate of Vector<float> * Matrix<float>
        | DTWishart of float * Matrix<float>

    [<AbstractClass>]
    type Context() =
        let rnd' = Random()
        member this.rnd with get() = rnd'
        abstract sample : string * DistributionType * (Sample option -> Sample * float) -> Sample 
        abstract AddLikelihood : float -> unit
        abstract yieldPrevious : unit -> bool

    [<AbstractClass>]
    type Distribution<'v>(dt: DistributionType) =
        member this.dt with get() = dt
        abstract sample : Context * Sample option -> 'v
        abstract loglikelihood : 'v -> float

    type CacheEntry =
        CacheEntry of string * Sample * float * DistributionType

    type MHAlgorithm(cache : Map<string, CacheEntry>, likelihood) =
        inherit Context()
        let mutable lastLikelihood = likelihood
        let mutable currLikelihood = Double.NegativeInfinity
        let mutable lastCache = cache
        let mutable lastUsedVars = Set.empty
        let mutable currCache = cache
        let mutable currUsedVars = Set.empty
        let mutable changedVar = None
        let getLikelihoodFromCache variable (cache: Map<_,_>) = 
                match variable with
                | Some(key) ->
                    match cache.TryFind(key) with
                    | Some(CacheEntry(_, _, l, _)) -> l
                    | None -> Double.NegativeInfinity
                | None -> Double.NegativeInfinity
        let cloneCache source =
            Map(Seq.map (fun (kvp: System.Collections.Generic.KeyValuePair<string, CacheEntry>) -> (kvp.Key, kvp.Value)) source)
        new() = MHAlgorithm(Map.empty, Double.NegativeInfinity)
        override this.sample(key, dt, f) =
            currUsedVars <- currUsedVars.Add(key)
            match currCache.TryFind(key) with
            | Some (CacheEntry(key, v, l, dt')) when dt' = dt ->
                      v
            | Some (CacheEntry(key, v, l, dt')) ->
                      currCache <- currCache.Remove(key)
                      let v', l' = f (Some v)
                      currCache <- currCache.Add(key, CacheEntry(key, v', l', dt))
                      v'
            | None -> let v, l = f None
                      currCache <- currCache.Add(key, CacheEntry(key, v, l, dt))
                      v
        override this.AddLikelihood(likelihood) = 
            if Double.IsNegativeInfinity(currLikelihood) then
                currLikelihood <- likelihood
            else
                currLikelihood <- currLikelihood + likelihood
        override this.yieldPrevious () =
//            let l = Seq.sumBy (fun key -> (getLikelihoodFromCache (Some key) currCache)) currUsedVars
//            let pl = Seq.sumBy (fun key -> (getLikelihoodFromCache (Some key) lastCache)) lastUsedVars
            let alpha = currLikelihood - lastLikelihood //- l  + pl
            let r = Math.Min(0., alpha)
            let u = Math.Log(this.rnd.NextDouble())
            let result = r <= u
            if result then
                currCache <- cloneCache lastCache
                currUsedVars <- Set(lastUsedVars)
            else
                lastCache <- cloneCache currCache
                lastUsedVars <- Set(currUsedVars)
                lastLikelihood <- currLikelihood

            let count = currUsedVars.Count
            if count > 0 then
                let index = this.rnd.Next(0, count)
                let keys = currUsedVars |> Seq.toArray;
                let key = keys.[index]
                changedVar <- Some key
                currCache <- currCache.Remove(key)

            currLikelihood <- Double.NegativeInfinity
            currUsedVars <- Set.empty
            result

    type Sampler<'v> = 
        | Sampler of (Context -> 'v)
    
    let likelihoodOf (dist: Distribution<'v>) (v: 'v) =
        dist.loglikelihood v

    type SamplerBuilder() =
        member this.Return(v : 'v) : Sampler<'v> =
            Sampler(fun ctx -> v)
        member this.ReturnFrom(m : Sampler<'v>) : Sampler<'v> = m
        member this.Bind(Sampler(s), f : 'a -> Sampler<'v>) =
            Sampler(fun ctx -> let (Sampler f') = f(s(ctx))
                               f'(ctx))
        member this.Combine(a, b) =
            this.Bind(a, b)

        [<CustomOperation("observe", MaintainsVariableSpaceUsingBind = true)>]
        member this.Observe(Sampler fvar, [<ProjectionParameter>] guard : 'vars -> ('d * 'v) seq) : Sampler<'vars>=
            Sampler(fun ctx -> let vars = fvar(ctx)
                               let sq = guard(vars)
                               let likelihood = Seq.fold (fun l (dist, v) -> l + (likelihoodOf dist v)) 0. sq
                               ctx.AddLikelihood likelihood
                               vars)
        [<CustomOperation("observeW", MaintainsVariableSpaceUsingBind = true)>]
        member this.ObserveWeighted(Sampler fvar, [<ProjectionParameter>] guard : 'vars -> (('d * float)seq * 'v) seq) : Sampler<'vars>=
            let distW dists v = Seq.sumBy (fun (dist, w) -> (likelihoodOf dist v) + (Math.Log w)) dists
            Sampler(fun ctx -> let vars = fvar(ctx)
                               let sq = guard(vars)
                               let likelihood = Seq.fold (fun l (dists, v) -> l + (distW dists v)) 0. sq
                               ctx.AddLikelihood likelihood
                               vars)
        member this.Zero() : Sampler<unit> =
            Sampler(fun ctx -> ())
        member inline this.Using(r,f) = Sampler(fun s -> 
            use rr = r in let (Sampler g) = f rr in g s)

        [<CustomOperation("where", MaintainsVariableSpaceUsingBind = true)>]
        member this.Where(Sampler fvar, [<ProjectionParameter>] guard : 'vars -> bool) : Sampler<'vars> =
            Sampler(fun ctx -> let vars = fvar(ctx)
                               if guard(vars) then ctx.AddLikelihood Double.NegativeInfinity
                               vars)

        member this.For(sq:seq<'V>, f:'V -> Sampler<unit>) = 
            let rec loop (en:System.Collections.Generic.IEnumerator<_>) = 
              if en.MoveNext() then this.Bind(f en.Current, fun _ -> loop en)
              else this.Zero()
            Sampler(fun ctx -> let (Sampler result) = this.Using(sq.GetEnumerator(), loop)
                               result(ctx))
        member this.Delay(f) = f
        member this.Run(f) = f()


    let sampler = SamplerBuilder()

    // Distributions

    let distSample (dist: Distribution<_>) s id (ctx: Context) =
        ctx.sample(id, dist.dt, fun pv -> let v = dist.sample(ctx, pv) in (s v, likelihoodOf dist v))

    type Beta(a, b) =
        inherit Distribution<float>(DTBeta(a, b))
        override this.sample(ctx, pv) = Beta.Sample(ctx.rnd, a, b)
        override this.loglikelihood(v) = Beta.PDFLn(a, b, v)

    let beta id a b =
        let dist = Beta(a, b)
        Sampler(fun ctx -> let (Real v) = distSample dist Real id ctx
                           v)

    type Bernoulli(p) =
        inherit Distribution<bool>(DTBernoulli p)
        let intToBool v = if v = 0 then false else true
        let boolToInt v = if v then 1 else 0
        override this.sample(ctx, pv) =
            match pv with
            | None -> Binomial.Sample(ctx.rnd, p, 1) |> intToBool
            | Some (Bool v) -> not v
        override this.loglikelihood(v) = Binomial.PMFLn(p, 1, (boolToInt v))

    let bernoulli id p =
        let dist = Bernoulli(p)
        Sampler(fun ctx -> let (Bool v) = distSample dist Bool id ctx
                           v)

    type Discrete(min, max) =
        inherit Distribution<int>(DTDiscrete(min, max))
        override this.sample(ctx, pv) = DiscreteUniform.Sample(ctx.rnd, min, max)
        override this.loglikelihood(v) = DiscreteUniform.PMFLn(min, max, v)

    let discrete id min max =
        let dist = Discrete(min, max)
        Sampler(fun ctx -> let (Integer v) = distSample dist Integer id ctx
                           v)

    type Gaussian(mean, stdDev) =
        inherit Distribution<float>(DTGaussian(mean, stdDev))
        override this.sample(ctx, pv) =
            match pv with
            | None -> Normal.Sample(ctx.rnd, mean, stdDev)
            | Some (Real v) -> Normal.Sample(ctx.rnd, v, stdDev)
        override this.loglikelihood(v) = Normal.PDFLn(mean, stdDev, v)

    let gaussian id mean stdDev =
        let dist = Gaussian(mean, stdDev)
        Sampler(fun ctx -> let (Real v) = distSample dist Real id ctx
                           v)

    type Gamma(shape, scale) =
        inherit Distribution<float>(DTGamma(shape, scale))
        override this.sample(ctx, pv) = Gamma.Sample(shape, 1. / scale)
        override this.loglikelihood(v) = Gamma.PDFLn(shape, 1. / scale, v)

    let gamma id shape scale =
        let dist = Gamma(shape, scale)
        Sampler(fun ctx -> let (Real v) = distSample dist Real id ctx
                           v)
    
    type Uniform(min, max) =
        inherit Distribution<float>(DTUniform(min, max))
        override this.sample(ctx, pv) = ContinuousUniform.Sample(min, max)
        override this.loglikelihood(v) = ContinuousUniform.PDFLn(min, max, v)

    let uniform id min max =
        let dist = Uniform(min, max)
        Sampler(fun ctx -> let (Real v) = distSample dist Real id ctx
                           v)

    type GaussianM(mean, variance) =
        inherit Distribution<Vector<float>>(DTGaussianMultivariate(mean, variance))
        override this.sample(ctx, pv) = 
            match pv with
            | None ->
                let m = MatrixNormal.Sample(ctx.rnd, (mean.ToColumnMatrix()), variance, DenseMatrix.identity(1))
                m.Column(0)
            | Some (Vec v) ->
                let m = MatrixNormal.Sample(ctx.rnd, (v.ToColumnMatrix()), variance, DenseMatrix.identity(1))
                m.Column(0)
        override this.loglikelihood(v) = 
            let l = MatrixNormal((mean.ToColumnMatrix()), variance, DenseMatrix.identity(1)).Density(v.ToColumnMatrix())
            Math.Log l

    let gaussianM id mean variance =
        let dist = GaussianM(mean, variance)
        Sampler(fun ctx -> let (Vec v) = distSample dist Vec id ctx
                           v)
    type Wishart(shape : float, scale: Matrix<float>) =
        inherit Distribution<Matrix<float>>(DTWishart(shape, scale))
        let mRate = MicrosoftResearch.Infer.Maths.PositiveDefiniteMatrix(scale.Inverse().ToArray())
        override this.sample(ctx, pv) =
                let sample = MicrosoftResearch.Infer.Distributions.Wishart.SampleFromShapeAndRate(shape, mRate)
                DenseMatrix.ofArray2(sample.ToArray())
        override this.loglikelihood(v) =
                let mv = MicrosoftResearch.Infer.Maths.PositiveDefiniteMatrix(v.ToArray())
                let l = MicrosoftResearch.Infer.Distributions.Wishart.GetLogProb(mv, shape, mRate)
                l

    let wishart id shape scale =
        let dist = Wishart(shape, scale)
        Sampler(fun ctx -> let (Mat v) = distSample dist Mat id ctx
                           v)

    // Query and results aggregation

    let vec = DenseVector.ofList

    let mat = DenseMatrix.ofColumnList

    let matId = DenseMatrix.identity

    let matNormal mean variance =
        let meanM = (vec mean).ToColumnMatrix()
        MatrixNormal(meanM, mat variance, matId 1) 

    let sampleSeq ctx (Sampler s) = 
        Seq.unfold(fun previous ->
            let v = s(ctx)
            match (previous, ctx.yieldPrevious()) with
            | (None, _) | (Some _, false) -> Some(v, Some v)
            | (Some pv, _) -> Some(pv, previous)) None

//    let averageByItem s size =
//        Array.init size (fun i -> Seq.averageBy (fun item -> Array.get item i) s)

    let hist samples =
        let list = List.ofSeq samples
        let total = float (list.Length)
        Seq.countBy id list |> Seq.map (fun (key, count) -> (key, (float count) / total)) |> Seq.toList

    let mhQuery sampler skip lag =
        sampleSeq (MHAlgorithm()) sampler 
            |> Seq.skip skip 
            |> Seq.windowed lag 
            |> Seq.map (Seq.last) 

    // Examples

    let s1 = sampler {
        let! p = beta "p" 1. 1.
        observe ([true; true; true; true; false] |> Seq.map (fun v -> (Bernoulli(p), v)))
        return p
    }
    
//    let s1Results = sampleSeq (MHAlgorithm()) s1 |> Seq.take 100 |> Seq.toList
//    let s1ResultAverage = Seq.average s1Results
    
    let s2Observations = List.init 100 float |> List.map (fun i -> (i, 20.5 + i * 5.5 + i * i * -1.5 + i * i * i * 0.4))
    let s2 = sampler {
        let! order = discrete "order" 1 10
        let id = "w" + order.ToString()
        let! w = gaussianM id (vec (List.init order (fun _ -> 0.))) (DenseMatrix.identity order)
        let! noise = gamma "noise" 1. 1.
        let observation = Seq.map (fun (x, y) -> ((List.init order (fun i -> (pown x i) * w.[i]) |> List.sum), y)) s2Observations |> List.ofSeq
        observe(Seq.map (fun (y', y) -> (Gaussian(y', noise), y)) observation)
        return (order, w);
    }

    //let s2Results = mhQuery s2 100 100 |> Seq.take 1000 |> Seq.toList
    //printfn "s2Results %A" s2Results
    //printfn "last entry %A" (Seq.last s2Results)
//
//    let s2weights = Seq.groupBy fst s2Results 
//                    |> Seq.map (fun (key, items) -> (key, averageByItem (Seq.map snd items) key))
//                    |> Map.ofSeq

    let s3Observation = List.init 100 (fun _ -> Normal.Sample(2.5, 1.2))
    let s3 = sampler {
        let! mean = gaussian "mean" 0. 10.
        let! stdDev = gamma "stdDev" 1. 1.
        let gDist = Gaussian(mean, stdDev)
        observe(Seq.map(fun o -> (gDist, o)) s3Observation)
        return (mean, stdDev)
    }

    // let s3Results = mhQuery s3 100 100 |> Seq.toList
    // let s3Avgs = (Seq.averageBy fst s3Results, Seq.averageBy snd s3Results)

    let s4Observation = List.init 100 (fun _ -> if Beta.Sample(1.,1.) > 0.7 then Normal.Sample(2.5, 1.) else Normal.Sample(-2.5, 1.))
    let s4 = sampler {
        let! p = beta "p" 1. 1.
        let! mean1 = gaussian "mean1" 0. 1.
        let! mean2 = gaussian "mean2" 0. 1.
        let! noise = gamma "noise" 1. 1.
        let gDist1 = Gaussian(mean1, noise)
        let gDist2 = Gaussian(mean2, noise)
        let gDistMix = [(gDist1, p);(gDist2, (1. - p))] |> Seq.ofList
        observeW(Seq.map (fun o -> (gDistMix, o)) s4Observation)
        return [|mean1; mean2; p; noise|]
    }
    
    //let s4Results = sampleSeq (MHAlgorithm()) s4 |> Seq.skip 100 |> Seq.take 1000 |> Seq.toList
    //let s4Avgs = averageByItem s4Results 4
    //MathNet.Numerics.Statistics.Mcmc.MetropolisHastingsSampler()
    let s5Observation = List.init 20 (fun _ -> Samplers.binomial(0.72))
    let s5 = sampler {
        let! a = gamma "a" 2. 20.
        let! b = gamma "b" 2. 20.
        let! prior = beta "prior" a b
        let coin = Bernoulli(prior)
        observe(Seq.map(fun o -> (coin, o)) s5Observation)
        return [|a;b;prior|]
    }

//    let s5Results = let res = mhQuery s5 100 100 
//                              |> Seq.take 1000
//                    averageByItem res 3
    

    let s6RealDist = matNormal [1.5;-2.2] [[1.;0.];[0.;1.]]

    let s6Observations = List.init 100 (fun _ -> s6RealDist.Sample().Column(0))

    let s6 = sampler {
        let! mean = gaussianM "mean" (vec [0.;0.]) (mat [[1.;0.];[0.;1.]])
        let variance = mat [[1.;0.];[0.;1.]]
        let g1 = GaussianM(mean, variance)
        observe(seq{for o in s6Observations -> (g1, o)})
        return mean |> Vector.toArray
    }

//    let s6Results = mhQuery s6 100 100 |> Seq.take 1000 |> Seq.toList
//    let s6MeanEstimate = averageByItem s6Results 2
//    printfn "Multivariate gaussian mean estimate %A" s6MeanEstimate

    let dataDir = @"..\Data\Market\"

    open Deedle

    let loadStock symbol =
            Frame.ReadCsv (dataDir + symbol + ".csv")
            |> Frame.indexRowsDate "Date"

    let dailyReturns (frame : Frame<DateTime, string>) =
        let result = log(frame?Close) - log(frame?Open)
        result
        //let returns = Seq.zip frame?Close.Values frame?Open.Values
        //returns |> Seq.map (fun (c, o) -> log(c) - log(o))

    let stockReturns stocks =
        let frame = Frame.ofColumns(Seq.map(fun s -> (s, dailyReturns(loadStock s))) stocks)
        frame

    let s7Observations =
        let stocks = ["GOOG"; "GLD"; "SPY"]
        let result = stockReturns stocks
        let arr = result.DropSparseRows().ToArray2D()
        let l = Array2D.length1 arr
        let w = Array2D.length2 arr
        Array.init l (fun i -> DenseVector.ofArray (Array.init w (fun j -> arr.[i,j])))

    let s7 = sampler {
        let! mean = gaussianM "mean" (DenseVector.zero(3)) (DenseMatrix.identity(3))
        let! variance = wishart "variance" 2. (DenseMatrix.identity(3))
        let dist = GaussianM(mean, variance)
        observe(Seq.map(fun o -> (dist, o)) s7Observations)
        return (mean, variance)
    }

    let s7ResultAvg = mhQuery s7 100 100 
                        |> Seq.take 1000
                        |> Seq.last

    let stop = ()

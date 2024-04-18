-- Collects data related to the connections in the ProbTime program so that it
-- can be included in the system specification JSON file.

include "argparse.mc"
include "ast.mc"
include "compile.mc"
include "task-data.mc"

lang RtpplConnectionBase = RtpplAst
  type PortSpec = {
    srcId : Name,
    portId : Option String
  }

  type ConnectionSpec = {
    from : PortSpec,
    to : PortSpec
  }

  sem rtpplPortSpecToPortSpec : RtpplPortSpec -> PortSpec
  sem rtpplPortSpecToPortSpec =
  | PortSpecRtpplPortSpec {port = {v = srcId}, id = Some {v = portId}} ->
    {srcId = srcId, portId = Some portId}
  | PortSpecRtpplPortSpec {port = {v = srcId}, id = None ()} ->
    {srcId = srcId, portId = None ()}

  sem portSpecToString : PortSpec -> String
  sem portSpecToString =
  | {srcId = src, portId = Some portId} ->
    join [nameGetStr src, "-", portId]
  | {srcId = src, portId = None _} ->
    nameGetStr src

  sem portSpecCmp : PortSpec -> PortSpec -> Int
  sem portSpecCmp l =
  | r ->
    let c = nameCmp l.srcId r.srcId in
    if eqi c 0 then
      switch (l.portId, r.portId)
      case (Some lid, Some rid) then cmpString lid rid
      case (None _, Some _) then -1
      case (Some _, None _) then 1
      case (None _, None _) then 0
      end
    else c

  sem connectionSpecCmp : ConnectionSpec -> ConnectionSpec -> Int
  sem connectionSpecCmp l =
  | r ->
    let c = portSpecCmp l.from r.from in
    if eqi c 0 then portSpecCmp l.to r.to
    else c
end

lang RtpplConnectionMessageSize = RtpplConnectionBase
  -- NOTE(larshum, 2024-04-18): The behavior of this function is based on the
  -- current approach to marshaling data. If we update that, or extend it to
  -- support more kinds of data types, this function should be updated
  -- accordingly.
  sem computeTypeMessageSize : RtpplType -> (Int, Int)
  sem computeTypeMessageSize =
  | ty ->
    -- NOTE(larshum, 2024-04-18): All messages include two 64-bit integers
    -- encoding the size of the remainder of the message (excluding itself) and
    -- a timestamp. We use a helper function to compute the size of the message
    -- payload without counting these extra 64-bit integers multiple times.
    match computeTypeMessageSizeH ty with (base, var) in
    (addi base 16, var)

  sem computeTypeMessageSizeH : RtpplType -> (Int, Int)
  sem computeTypeMessageSizeH =
  | IntRtpplType _ | FloatRtpplType _ -> (8, 0)
  | RecordRtpplType {fields = fields} ->
    foldl
      (lam acc. lam f.
        match acc with (base, var) in
        match computeTypeMessageSizeH f.ty with (base2, var2) in
        (addi base base2, addi var var2))
      (0, 0) fields
  | DistRtpplType {ty = ty, info = info} ->
    match computeTypeMessageSizeH ty with (base, 0) then
      -- NOTE(larshum, 2024-04-18): Each sample of a distribution contains the
      -- data of the base type (the returned value) and a 64-bit floating-point
      -- weight.
      (0, addi base 8)
    else errorSingle [info] "Found nested distribution type"
  | ty -> errorSingle [get_RtpplType_info ty] "Found unsupported type in computeTypeMessageSizeH"

  sem baseMessageSize : RtpplType -> Int
  sem baseMessageSize =
  | ty -> match computeTypeMessageSize ty with (baseSz, _) in baseSz

  sem perParticleMessageSize : RtpplType -> Int
  sem perParticleMessageSize =
  | ty -> match computeTypeMessageSize ty with (_, perPartSz) in perPartSz
end

lang RtpplConnectionTypes = RtpplConnectionBase
  sem findConnectionTypes : RtpplProgram -> Map ConnectionSpec RtpplType
  sem findConnectionTypes =
  | ProgramRtpplProgram p ->
    -- 1. Collect the types of all ports declared in templates.
    let templatePortTypes = foldl collectTemplatePortTypes (mapEmpty nameCmp) p.tops in

    -- 2. Compute the types of all task ports based on the templates.
    let taskPortTypes = computeTaskPortTypes templatePortTypes p.main in

    -- 3. Compute the types of all connections based on the types of task
    -- ports. This works because all connections involve at least one task.
    computeConnectionTypes taskPortTypes p.main

  sem collectTemplatePortTypes : Map Name (Map String RtpplType) -> RtpplTop
                              -> Map Name (Map String RtpplType)
  sem collectTemplatePortTypes acc =
  | TemplateDefRtpplTop {id = {v = id}, body = {ports = ports}} ->
    let portTypes = foldl collectPortType (mapEmpty cmpString) ports in
    mapInsert id portTypes acc
  | _ ->
    acc

  sem collectPortType : Map String RtpplType -> RtpplPort
                     -> Map String RtpplType
  sem collectPortType acc =
  | InputRtpplPort {id = {v = id}, ty = ty}
  | OutputRtpplPort {id = {v = id}, ty = ty} ->
    mapInsert id ty acc

  sem computeTaskPortTypes : Map Name (Map String RtpplType) -> RtpplMain
                          -> Map PortSpec RtpplType
  sem computeTaskPortTypes templatePortTypes =
  | MainRtpplMain {tasks = tasks} ->
    foldl (findTaskPortTypes templatePortTypes) (mapEmpty portSpecCmp) tasks

  sem findTaskPortTypes : Map Name (Map String RtpplType)
                       -> Map PortSpec RtpplType -> RtpplTask
                       -> Map PortSpec RtpplType
  sem findTaskPortTypes templatePortTypes acc =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    match mapLookup tid templatePortTypes with Some portTypes then
      mapFoldWithKey
        (lam acc. lam portId. lam portType.
          let portSpec = { srcId = id, portId = Some portId } in
          mapInsert portSpec portType acc)
        acc portTypes
    else errorSingle [info] "Task is defined in terms of unknown task template"

  sem computeConnectionTypes : Map PortSpec RtpplType -> RtpplMain
                            -> Map ConnectionSpec RtpplType
  sem computeConnectionTypes taskPortTypes =
  | MainRtpplMain {connections = connections} ->
    foldl (addConnectionType taskPortTypes) (mapEmpty connectionSpecCmp) connections

  sem addConnectionType : Map PortSpec RtpplType -> Map ConnectionSpec RtpplType
                       -> RtpplConnection -> Map ConnectionSpec RtpplType
  sem addConnectionType taskPortTypes acc =
  | ConnectionRtpplConnection {from = from, to = to, info = info} ->
    let fromPortSpec = rtpplPortSpecToPortSpec from in
    let toPortSpec = rtpplPortSpecToPortSpec to in
    let connSpec = {from = fromPortSpec, to = toPortSpec} in
    let ty =
      match mapLookup fromPortSpec taskPortTypes with Some ty then ty
      else match mapLookup toPortSpec taskPortTypes with Some ty then ty
      else errorSingle [info] "Failed to find type of connection"
    in
    mapInsert connSpec ty acc
end

-- This language computes the frequency at which messages are sent through each
-- connection. For connections where a sensor is the source, this is simply
-- computed based on its annotated maximum rate. When the source is a task, we
-- count the maximum number of times a task writes to a particular port in one
-- period. If the code writes to a port in a loop, we cannot (easily) determine
-- the count - we represent this using 'Dynamic'. Based on this count and the
-- period of a task, we can compute the peak message frequency.
lang RtpplConnectionMessageFrequency = RtpplConnectionBase + RtpplTaskPeriod
  syn WriteFreq =
  | Fixed Float
  | Dynamic ()

  sem mapWriteFreq : (Float -> Float -> Float) -> WriteFreq -> WriteFreq -> WriteFreq
  sem mapWriteFreq f lc =
  | rc ->
    mapWriteFreqH f (lc, rc)

  sem mapWriteFreqH : (Float -> Float -> Float) -> (WriteFreq, WriteFreq) -> WriteFreq
  sem mapWriteFreqH f =
  | (Fixed a, Fixed b) -> Fixed (f a b)
  | _ -> Dynamic ()

  sem findConnectionMessageFrequencies : RtpplProgram -> Map ConnectionSpec Float
  sem findConnectionMessageFrequencies =
  | prog & (ProgramRtpplProgram p) ->
    -- 1. Find the periods of all tasks (defined in task-data.mc)
    let taskPeriods = findProgramTaskPeriods prog in

    -- 2. Collect the write count for each output port of all task templates.
    let templateWriteCounts = foldl countTemplatePortWrites (mapEmpty nameCmp) p.tops in

    -- 3. Collect the write frequency of each output port. For sensors, we
    -- compute it directly based on the annotated max rate. For tasks, we use
    -- the write count for its corresponding template and the period of the
    -- task to compute the frequency.
    let portWriteFreq = findPortWriteFrequencies taskPeriods templateWriteCounts p.main in

    -- Construct a map from connections to write frequency based on the output
    -- port frequency.
    findConnectionFrequencies portWriteFreq p.main

  sem countTemplatePortWrites : Map Name (Map String WriteFreq) -> RtpplTop
                             -> Map Name (Map String WriteFreq)
  sem countTemplatePortWrites acc =
  | TemplateDefRtpplTop {id = {v = id}, body = {periodic = periodic}, info = info} ->
    let templatePortWrites =
      sfold_RtpplPeriodic_RtpplStmt
        countTemplatePortWritesStmt (mapEmpty cmpString) periodic
    in
    mapInsert id templatePortWrites acc
  | _ ->
    acc

  -- NOTE(larshum, 2024-04-18): We count all writes we can find directly. If we
  -- find a loop we enter the below function which counts any write as dynamic
  -- as we cannot in general know how many times a loop runs.
  sem countTemplatePortWritesStmt : Map String WriteFreq -> RtpplStmt
                                 -> Map String WriteFreq
  sem countTemplatePortWritesStmt acc =
  | WriteRtpplStmt {port = {v = portId}} ->
    mapInsertWith (mapWriteFreq addf) portId (Fixed 1.0) acc
  | ConditionRtpplStmt {thn = thn, els = els} ->
    let thnWrites = foldl countTemplatePortWritesStmt acc thn in
    let elsWrites = foldl countTemplatePortWritesStmt acc els in
    mapUnionWith (mapWriteFreq maxf) thnWrites elsWrites
  | ForLoopRtpplStmt {body = body} | WhileLoopRtpplStmt {body = body} ->
    foldl invalidateTemplatePortWritesStmt acc body
  | s ->
    acc

  sem invalidateTemplatePortWritesStmt : Map String WriteFreq -> RtpplStmt
                                      -> Map String WriteFreq
  sem invalidateTemplatePortWritesStmt acc =
  | WriteRtpplStmt {port = {v = portId}} ->
    mapInsertWith (lam. lam v. v) portId (Dynamic ()) acc
  | s ->
    sfold_RtpplStmt_RtpplStmt invalidateTemplatePortWritesStmt acc s

  sem findPortWriteFrequencies : Map Name Int -> Map Name (Map String WriteFreq)
                              -> RtpplMain -> Map PortSpec Float
  sem findPortWriteFrequencies taskPeriods templateWriteCounts =
  | MainRtpplMain {ext = ext, tasks = tasks} ->
    let pwf = foldl findSensorWriteFrequency (mapEmpty portSpecCmp) ext in
    foldl (findTaskPortWriteFrequency taskPeriods templateWriteCounts) pwf tasks

  sem findSensorWriteFrequency : Map PortSpec Float -> RtpplExt
                              -> Map PortSpec Float
  sem findSensorWriteFrequency acc =
  | SensorRtpplExt {id = {v = id}, r = r, info = info} ->
    let sensorPortSpec = { srcId = id, portId = None () } in
    let maxWriteFreq =
      match r with LiteralRtpplExpr {const = LitIntRtpplConst {value = {v = n}}} then
        divf 1e9 (int2float n)
      else errorSingle [info] "Sensor maximum rate must be a literal integer value"
    in
    mapInsert sensorPortSpec maxWriteFreq acc
  | _ ->
    acc

  sem findTaskPortWriteFrequency : Map Name Int -> Map Name (Map String WriteFreq)
                                -> Map PortSpec Float -> RtpplTask
                                -> Map PortSpec Float
  sem findTaskPortWriteFrequency taskPeriods templateWriteCounts acc =
  | TaskRtpplTask {id = {v = id}, templateId = {v = tid}, info = info} ->
    match mapLookup id taskPeriods with Some period then
      match mapLookup tid templateWriteCounts with Some writeCounts then
        mapFoldWithKey
          (lam acc. lam portId. lam countRepr.
            let portSpec = { srcId = id, portId = Some portId } in
            -- NOTE(larshum, 2024-04-18): We use a negative number of indicate
            -- that we failed to statically determine the write count.
            let count =
              match countRepr with Fixed f then f
              else match countRepr with Dynamic _ then -1.0
              else never
            in
            let writeFreq = mulf count (divf 1e9 (int2float period)) in
            mapInsert portSpec writeFreq acc)
          acc writeCounts
      else errorSingle [info] "Task is defined in terms of unknown task template"
    else errorSingle [info] "Failed to find period for task"

  sem findConnectionFrequencies : Map PortSpec Float -> RtpplMain -> Map ConnectionSpec Float
  sem findConnectionFrequencies portFrequencies =
  | MainRtpplMain {connections = connections} ->
    foldl (addConnectionFrequency portFrequencies) (mapEmpty connectionSpecCmp) connections

  sem addConnectionFrequency : Map PortSpec Float -> Map ConnectionSpec Float
                            -> RtpplConnection -> Map ConnectionSpec Float
  sem addConnectionFrequency portFrequencies acc =
  | ConnectionRtpplConnection {from = from, to = to} ->
    let fromPortSpec = rtpplPortSpecToPortSpec from in
    let toPortSpec = rtpplPortSpecToPortSpec to in
    let connSpec = {from = fromPortSpec, to = toPortSpec} in
    let freq =
      match mapLookup fromPortSpec portFrequencies with Some freq then freq
      else 0.0
    in
    mapInsert connSpec freq acc
end

lang RtpplConnectionData =
  RtpplConnectionMessageSize + RtpplConnectionTypes +
  RtpplConnectionMessageFrequency + RtpplCompileBase

  type ConnectionData = {
    from : PortSpec,
    to : PortSpec,
    ty : RtpplType,
    messageFrequency : Float
  }

  sem collectConnectionData : RtpplProgram -> [ConnectionData]
  sem collectConnectionData =
  | p & (ProgramRtpplProgram _) ->
    let connFreq = findConnectionMessageFrequencies p in
    let connType = findConnectionTypes p in
    let aliases = collectTypeAliases p in

    -- NOTE(larshum, 2024-04-18): Combine the connection frequencies and types
    -- into one complete representation of all connection data of interest. As
    -- both maps are constructed in the same way, they both have the same key,
    -- meaning we can combine them using intersection.
    let m = mapIntersectWith (lam l. lam r. (l, r)) connFreq connType in
    mapFoldWithKey
      (lam acc. lam conn. lam entry.
        match conn with {from = from, to = to} in
        match entry with (freq, ty) in
        let ty = resolveTypeAlias aliases ty in
        cons {from = from, to = to, ty = ty, messageFrequency = freq} acc)
      [] m

  sem collectTypeAliases : RtpplProgram -> Map Name RtpplType
  sem collectTypeAliases =
  | ProgramRtpplProgram p ->
    foldl collectTypeAliasesTop (mapEmpty nameCmp) p.tops

  sem collectTypeAliasesTop : Map Name RtpplType -> RtpplTop -> Map Name RtpplType
  sem collectTypeAliasesTop aliases =
  | TypeAliasRtpplTop {id = {v = id}, ty = ty} ->
    mapInsert id ty aliases
  | _ ->
    aliases
end

lang RtpplTestLang = RtpplConnectionMessageSize
end

mexpr

use RtpplTestLang in

let i = NoInfo () in
let ty1 = IntRtpplType {info = i} in
let ty2 = FloatRtpplType {info = i} in
let ty3 = RecordRtpplType {
  info = i, fields = [
    {id = {i = i, v = "a"}, ty = ty1},
    {id = {i = i, v = "b"}, ty = ty2}
  ]
} in
let ty4 = RecordRtpplType {
  info = i, fields = [
    {id = {i = i, v = "a"}, ty = ty1},
    {id = {i = i, v = "b"}, ty = ty1},
    {id = {i = i, v = "c"}, ty = ty1},
    {id = {i = i, v = "d"}, ty = ty1}
  ]
} in
let ty5 = DistRtpplType {
  ty = ty2, info = i
} in
let ty6 = DistRtpplType {
  ty = ty4, info = i
} in
utest computeTypeMessageSize ty1 with (24, 0) in
utest computeTypeMessageSize ty2 with (24, 0) in
utest computeTypeMessageSize ty3 with (32, 0) in
utest computeTypeMessageSize ty4 with (48, 0) in
utest computeTypeMessageSize ty5 with (16, 16) in
utest computeTypeMessageSize ty6 with (16, 40) in
()
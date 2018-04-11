@inline isexpr(@nospecialize(stmt), head::Symbol) = isa(stmt, Expr) && stmt.head === head
@eval Core.UpsilonNode() = $(Expr(:new, Core.UpsilonNode))
Core.PhiNode() = Core.PhiNode(Any[], Any[])

struct Argument
    n::Int
end

struct GotoIfNot
    cond
    dest::Int
    GotoIfNot(@nospecialize(cond), dest::Int) = new(cond, dest)
end

struct ReturnNode
    val
    ReturnNode(@nospecialize(val)) = new(val)
    # unassigned val indicates unreachable
    ReturnNode() = new()
end

"""
Like UnitRange{Int}, but can handle the `last` field, being temporarily
< first (this can happen during compacting)
"""
struct StmtRange <: AbstractUnitRange{Int}
    first::Int
    last::Int
end
first(r::StmtRange) = r.first
last(r::StmtRange) = r.last
start(r::StmtRange) = 0
done(r::StmtRange, state) = r.last - r.first < state
next(r::StmtRange, state) = (r.first + state, state + 1)

StmtRange(range::UnitRange{Int}) = StmtRange(first(range), last(range))

struct BasicBlock
    stmts::StmtRange
    #error_handler::Bool
    preds::Vector{Int}
    succs::Vector{Int}
end
function BasicBlock(stmts::StmtRange)
    BasicBlock(stmts, Int[], Int[])
end
function BasicBlock(old_bb, stmts)
    BasicBlock(stmts, #= old_bb.error_handler, =# old_bb.preds, old_bb.succs)
end
copy(bb::BasicBlock) = BasicBlock(bb.stmts, #= bb.error_handler, =# copy(bb.preds), copy(bb.succs))

struct CFG
    blocks::Vector{BasicBlock}
    index::Vector{Int}
end

function block_for_inst(index, inst)
    searchsortedfirst(index, inst, lt=(<=))
end
block_for_inst(cfg::CFG, inst) = block_for_inst(cfg.index, inst)

function compute_basic_blocks(stmts::Vector{Any})
    jump_dests = IdSet{Int}(1)
    # First go through and compute jump destinations
    for (idx, stmt) in pairs(stmts)
        # Terminators
        if isa(stmt, Union{GotoIfNot, GotoNode, ReturnNode})
            if isa(stmt, GotoIfNot)
                push!(jump_dests, idx+1)
                push!(jump_dests, stmt.dest)
            else
                # This is a fake dest to force the next stmt to start a bb
                idx < length(stmts) && push!(jump_dests, idx+1)
                if isa(stmt, GotoNode)
                    push!(jump_dests, stmt.label)
                end
            end
        elseif isa(stmt, Expr) && stmt.head === :leave
            # :leave terminates a BB
            push!(jump_dests, idx+1)
        elseif isa(stmt, Expr) && stmt.head == :enter
            # :enter starts/ends a BB
            push!(jump_dests, idx)
            push!(jump_dests, idx+1)
            # The catch block is a jump dest
            push!(jump_dests, stmt.args[1])
        end
    end
    bb_starts = sort(collect(jump_dests))
    for i = length(stmts):-1:1
        if stmts[i] != nothing
            push!(bb_starts, i+1)
            break
        end
    end
    # Compute ranges
    basic_block_index = Int[]
    blocks = BasicBlock[]
    sizehint!(blocks, length(bb_starts)-1)
    for (first, last) in Iterators.zip(bb_starts, Iterators.drop(bb_starts, 1))
        push!(basic_block_index, first)
        push!(blocks, BasicBlock(StmtRange(first, last-1)))
    end
    popfirst!(basic_block_index)
    # Compute successors/predecessors
    for (num, b) in pairs(blocks)
        terminator = stmts[last(b.stmts)]
        # Conditional Branch
        if isa(terminator, GotoIfNot)
            block′ = block_for_inst(basic_block_index, terminator.dest)
            push!(blocks[block′].preds, num)
            push!(b.succs, block′)
        end
        if isa(terminator, GotoNode)
            block′ = block_for_inst(basic_block_index, terminator.label)
            push!(blocks[block′].preds, num)
            push!(b.succs, block′)
        elseif !isa(terminator, ReturnNode)
            if isa(terminator, Expr) && terminator.head == :enter
                # :enter gets a virtual edge to the exception handler and
                # the exception handler gets a virtual edge from outside
                # the function.
                # See the devdocs on exception handling in SSA form (or
                # bug Keno to write them, if you're reading this and they
                # don't exist)
                block′ = block_for_inst(basic_block_index, terminator.args[1])
                push!(blocks[block′].preds, num)
                push!(blocks[block′].preds, 0)
                push!(b.succs, block′)
            end
            if num + 1 <= length(blocks)
                push!(blocks[num+1].preds, num)
                push!(b.succs, num+1)
            end
        end
    end
    CFG(blocks, basic_block_index)
end

function first_insert_for_bb(code, cfg, block)
    for idx in cfg.blocks[block].stmts
        stmt = code[idx]
        if !isa(stmt, LabelNode) && !isa(stmt, PhiNode)
            return idx
        end
    end
end


struct NewNode
    # Insertion position (interpretation depends on which array this is in)
    pos::Int
    # For BB purposes, attaches to the BB of the instruction before `pos`
    reverse_affinity::Bool
    # The type of the instruction to insert
    typ::Any
    # The node itself
    node::Any
    # The index into the line number table of this entry
    line::Int
end
function NewNode(nnode::NewNode; pos=nnode.pos, reverse_affinity=nnode.reverse_affinity,
                                 typ=nnode.typ, node=nnode.node, line=nnode.line)
    NewNode(pos, reverse_affinity, typ, node, line)
end

struct IRCode
    stmts::Vector{Any}
    types::Vector{Any}
    lines::Vector{Int}
    argtypes::Vector{Any}
    cfg::CFG
    new_nodes::Vector{NewNode}
    mod::Module
    meta::Vector{Any}

    function IRCode(stmts::Vector{Any}, types::Vector{Any}, lines::Vector{Int}, cfg::CFG, argtypes::Vector{Any}, mod::Module, meta::Vector{Any})
        return new(stmts, types, lines, argtypes, cfg, NewNode[], mod, meta)
    end
    function IRCode(ir::IRCode, stmts::Vector{Any}, types::Vector{Any}, lines::Vector{Int}, cfg::CFG, new_nodes::Vector{NewNode})
        return new(stmts, types, lines, ir.argtypes, cfg, new_nodes, ir.mod, ir.meta)
    end
end

function getindex(x::IRCode, s::SSAValue)
    if s.id <= length(x.stmts)
        return x.stmts[s.id]
    else
        return x.new_nodes[s.id - length(x.stmts)].node
    end
end

function setindex!(x::IRCode, repl, s::SSAValue)
    @assert s.id <= length(x.stmts)
    x.stmts[s.id] = repl
    nothing
end


struct OldSSAValue
    id::Int
end

struct NewSSAValue
    id::Int
end

mutable struct UseRefIterator
    stmt::Any
end
getindex(it::UseRefIterator) = it.stmt

struct UseRef
    urs::UseRefIterator
    use::Int
end

struct OOBToken
end

struct UndefToken
end

function getindex(x::UseRef)
    stmt = x.urs.stmt
    if isa(stmt, Expr) && stmt.head === :(=)
        rhs = stmt.args[2]
        if isa(rhs, Expr) && is_relevant_expr(rhs)
            x.use > length(rhs.args) && return OOBToken()
            return rhs.args[x.use]
        end
        x.use == 1 || return OOBToken()
        return rhs
    elseif isa(stmt, Expr) && is_relevant_expr(stmt)
        x.use > length(stmt.args) && return OOBToken()
        return stmt.args[x.use]
    elseif isa(stmt, GotoIfNot)
        x.use == 1 || return OOBToken()
        return stmt.cond
    elseif isa(stmt, ReturnNode) || isa(stmt, PiNode) || isa(stmt, UpsilonNode)
        isdefined(stmt, :val) || return OOBToken()
        x.use == 1 || return OOBToken()
        return stmt.val
    elseif isa(stmt, PhiNode) || isa(stmt, PhiCNode)
        x.use > length(stmt.values) && return OOBToken()
        isassigned(stmt.values, x.use) || return UndefToken()
        return stmt.values[x.use]
    else
        return OOBToken()
    end
end

function is_relevant_expr(e::Expr)
    return e.head in (:call, :invoke, :new, :(=), :(&),
                      :gc_preserve_begin, :gc_preserve_end,
                      :foreigncall, :isdefined, :copyast,
                      :undefcheck, :throw_undef_if_not)
end

function setindex!(x::UseRef, @nospecialize(v))
    stmt = x.urs.stmt
    if isa(stmt, Expr) && stmt.head === :(=)
        rhs = stmt.args[2]
        if isa(rhs, Expr) && is_relevant_expr(rhs)
            x.use > length(rhs.args) && throw(BoundsError())
            rhs.args[x.use] = v
        else
            x.use == 1 || throw(BoundsError())
            stmt.args[2] = v
        end
    elseif isa(stmt, Expr) && is_relevant_expr(stmt)
        x.use > length(stmt.args) && throw(BoundsError())
        stmt.args[x.use] = v
    elseif isa(stmt, GotoIfNot)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = GotoIfNot(v, stmt.dest)
    elseif isa(stmt, ReturnNode) || isa(stmt, UpsilonNode)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = typeof(stmt)(v)
    elseif isa(stmt, PiNode)
        x.use == 1 || throw(BoundsError())
        x.urs.stmt = typeof(stmt)(v, stmt.typ)
    elseif isa(stmt, PhiNode) || isa(stmt, PhiCNode)
        x.use > length(stmt.values) && throw(BoundsError())
        isassigned(stmt.values, x.use) || throw(BoundsError())
        stmt.values[x.use] = v
    else
        throw(BoundsError())
    end
    return x
end

function userefs(@nospecialize(x))
    if (isa(x, Expr) && is_relevant_expr(x)) ||
        isa(x, Union{GotoIfNot, ReturnNode, PiNode, PhiNode, PhiCNode, UpsilonNode})
        UseRefIterator(x)
    else
        ()
    end
end

start(it::UseRefIterator) = 1
function next(it::UseRefIterator, use)
    x = UseRef(it, use)
    v = x[]
    v === UndefToken() && return next(it, use + 1)
    x, use + 1
end
function done(it::UseRefIterator, use)
    x, _ = next(it, use)
    v = x[]
    v === OOBToken() && return true
    false
end

function scan_ssa_use!(used, @nospecialize(stmt))
    if isa(stmt, SSAValue)
        push!(used, stmt.id)
    end
    for useref in userefs(stmt)
        val = useref[]
        if isa(val, SSAValue)
            push!(used, val.id)
        end
    end
end

function ssamap(f, @nospecialize(stmt))
    urs = userefs(stmt)
    urs === () && return stmt
    for op in urs
        val = op[]
        if isa(val, SSAValue)
            op[] = f(val)
        end
    end
    urs[]
end

function foreachssa(f, @nospecialize(stmt))
    for op in userefs(stmt)
        val = op[]
        if isa(val, SSAValue)
            f(val)
        end
    end
end

function insert_node!(ir::IRCode, pos::Int, @nospecialize(typ), @nospecialize(val), reverse_affinity::Bool=false)
    line = ir.lines[pos]
    push!(ir.new_nodes, NewNode(pos, reverse_affinity, typ, val, line))
    return SSAValue(length(ir.stmts) + length(ir.new_nodes))
end

# For bootstrapping
function my_sortperm(v)
    p = Vector{Int}(undef, length(v))
    for i = 1:length(v)
        p[i] = i
    end
    sort!(p, Sort.DEFAULT_UNSTABLE, Order.Perm(Sort.Forward,v))
    p
end

mutable struct IncrementalCompact
    ir::IRCode
    result::Vector{Any}
    result_types::Vector{Any}
    result_lines::Vector{Int}
    result_bbs::Vector{BasicBlock}
    ssa_rename::Vector{Any}
    used_ssas::Vector{Int}
    late_fixup::Vector{Int}
    # This could be Stateful, but bootstrapping doesn't like that
    perm::Vector{Int}
    new_nodes_idx::Int
    # This supports insertion while compacting
    new_new_nodes::Vector{NewNode}  # New nodes that were before the compaction point at insertion time
    # TODO: Switch these two to a min-heap of some sort
    pending_nodes::Vector{NewNode}  # New nodes that were after the compaction point at insertion time
    pending_perm::Vector{Int}
    # State
    idx::Int
    result_idx::Int
    active_result_bb::Int
    function IncrementalCompact(code::IRCode)
        # Sort by position with reverse affinity nodes after regular ones
        perm = my_sortperm(Int[(code.new_nodes[i].pos*2 + Int(code.new_nodes[i].reverse_affinity)) for i in 1:length(code.new_nodes)])
        new_len = length(code.stmts) + length(code.new_nodes)
        result = Array{Any}(undef, new_len)
        result_types = Array{Any}(undef, new_len)
        result_lines = Array{Int}(undef, new_len)
        used_ssas = fill(0, new_len)
        ssa_rename = Any[SSAValue(i) for i = 1:new_len]
        late_fixup = Vector{Int}()
        new_new_nodes = NewNode[]
        pending_nodes = NewNode[]
        pending_perm = Int[]
        return new(code, result, result_types, result_lines, code.cfg.blocks, ssa_rename, used_ssas, late_fixup, perm, 1,
            new_new_nodes, pending_nodes, pending_perm,
            1, 1, 1)
    end

    # For inlining
    function IncrementalCompact(parent::IncrementalCompact, code::IRCode, result_offset)
        perm = my_sortperm(Int[code.new_nodes[i].pos for i in 1:length(code.new_nodes)])
        new_len = length(code.stmts) + length(code.new_nodes)
        ssa_rename = Any[SSAValue(i) for i = 1:new_len]
        used_ssas = fill(0, new_len)
        late_fixup = Vector{Int}()
        new_new_nodes = NewNode[]
        pending_nodes = NewNode[]
        pending_perm = Int[]
        return new(code, parent.result, parent.result_types, parent.result_lines, parent.result_bbs, ssa_rename, parent.used_ssas,
            late_fixup, perm, 1,
            new_new_nodes, pending_nodes, pending_perm,
            1, result_offset, parent.active_result_bb)
    end
end

struct TypesView
    ir::Union{IRCode, IncrementalCompact}
end
types(ir::Union{IRCode, IncrementalCompact}) = TypesView(ir)

function getindex(compact::IncrementalCompact, idx)
    if idx < compact.result_idx
        return compact.result[idx]
    else
        return compact.ir.stmts[idx]
    end
end

function getindex(compact::IncrementalCompact, ssa::SSAValue)
    @assert ssa.id < compact.result_idx
    return compact.result[ssa.id]
end

function getindex(compact::IncrementalCompact, ssa::OldSSAValue)
    id = ssa.id
    if id <= length(compact.ir.stmts)
        return compact.ir.stmts[id]
    end
    id -= length(compact.ir.stmts)
    if id <= length(compact.ir.new_nodes)
        return compact.ir.new_nodes[id].node
    end
    id -= length(compact.ir.new_nodes)
    return compact.pending_nodes[id].node
end

function getindex(compact::IncrementalCompact, ssa::NewSSAValue)
    return compact.new_new_nodes[ssa.id].node
end

function count_added_node!(compact, v)
    needs_late_fixup = isa(v, NewSSAValue)
    if isa(v, SSAValue)
        compact.used_ssas[v.id] += 1
    else
        for ops in userefs(v)
            val = ops[]
            if isa(val, SSAValue)
                compact.used_ssas[val.id] += 1
            elseif isa(val, NewSSAValue)
                needs_late_fixup = true
            end
        end
    end
    needs_late_fixup
end

function resort_pending!(compact)
    sort!(compact.pending_perm, DEFAULT_STABLE, Order.By(x->compact.pending_nodes[x].pos))
end

function insert_node!(compact::IncrementalCompact, before, @nospecialize(typ), @nospecialize(val), reverse_affinity::Bool=false)
    if isa(before, SSAValue)
        if before.id < compact.result_idx
            count_added_node!(compact, val)
            line = compact.result_lines[before.id]
            push!(compact.new_new_nodes, NewNode(before.id, reverse_affinity, typ, val, line))
            return NewSSAValue(length(compact.new_new_nodes))
        else
            line = compact.ir.lines[before.id]
            push!(compact.pending_nodes, NewNode(before.id, reverse_affinity, typ, val, line))
            push!(compact.pending_perm, length(compact.pending_nodes))
            resort_pending!(compact)
            os = OldSSAValue(length(compact.ir.stmts) + length(compact.ir.new_nodes) + length(compact.pending_nodes))
            push!(compact.ssa_rename, os)
            push!(compact.used_ssas, 0)
            return os
        end
    elseif isa(before, OldSSAValue)
        pos = before.id
        if pos > length(compact.ir.stmts)
            @assert reverse_affinity
            entry = compact.pending_nodes[pos - length(compact.ir.stmts) - length(compact.ir.new_nodes)]
            pos, reverse_affinity = entry.pos, entry.reverse_affinity
        end
        line = 0 #compact.ir.lines[before.id]
        push!(compact.pending_nodes, NewNode(pos, reverse_affinity, typ, val, line))
        push!(compact.pending_perm, length(compact.pending_nodes))
        resort_pending!(compact)
        os = OldSSAValue(length(compact.ir.stmts) + length(compact.ir.new_nodes) + length(compact.pending_nodes))
        push!(compact.ssa_rename, os)
        push!(compact.used_ssas, 0)
        return os
    elseif isa(before, NewSSAValue)
        before_entry = compact.new_new_nodes[before.id]
        push!(compact.new_new_nodes, NewNode(before_entry.pos, reverse_affinity, typ, val, before_entry.line))
        return NewSSAValue(length(compact.new_new_nodes))
    else
        error("Unsupported")
    end
end

function insert_node_here!(compact::IncrementalCompact, @nospecialize(val), @nospecialize(typ), ltable_idx::Int)
    if compact.result_idx > length(compact.result)
        @assert compact.result_idx == length(compact.result) + 1
        resize!(compact, compact.result_idx)
    end
    compact.result[compact.result_idx] = val
    compact.result_types[compact.result_idx] = typ
    compact.result_lines[compact.result_idx] = ltable_idx
    count_added_node!(compact, val)
    ret = SSAValue(compact.result_idx)
    compact.result_idx += 1
    ret
end

function getindex(view::TypesView, v::OldSSAValue)
    id = v.id
    if id <= length(view.ir.ir.types)
        return view.ir.ir.types[id]
    end
    id -= length(view.ir.ir.types)
    if id <= length(view.ir.ir.new_nodes)
        return view.ir.ir.new_nodes[id].typ
    end
    id -= length(view.ir.ir.new_nodes)
    return view.ir.pending_nodes[id].typ
end

function setindex!(compact::IncrementalCompact, @nospecialize(v), idx::SSAValue)
    @assert idx.id < compact.result_idx
    (compact.result[idx.id] === v) && return
    # Kill count for current uses
    for ops in userefs(compact.result[idx.id])
        val = ops[]
        if isa(val, SSAValue)
            @assert compact.used_ssas[val.id] >= 1
            compact.used_ssas[val.id] -= 1
        end
    end
    compact.result[idx.id] = v
    # Add count for new use
    if count_added_node!(compact, v)
        push!(compact.late_fixup, idx.id)
    end
end

function setindex!(compact::IncrementalCompact, @nospecialize(v), idx)
    if idx < compact.result_idx
        compact[SSAValue(idx)] = v
    else
        compact.ir.stmts[idx] = v
    end
    return nothing
end

function getindex(view::TypesView, idx)
    isa(idx, SSAValue) && (idx = idx.id)
    if isa(view.ir, IncrementalCompact) && idx < view.ir.result_idx
        return view.ir.result_types[idx]
    else
        ir = isa(view.ir, IncrementalCompact) ? view.ir.ir : view.ir
        if idx <= length(ir.types)
            return ir.types[idx]
        else
            return ir.new_nodes[idx - length(ir.types)].typ
        end
    end
end

function getindex(view::TypesView, idx::NewSSAValue)
    @assert isa(view.ir, IncrementalCompact)
    compact = view.ir
    compact.new_new_nodes[idx.id].typ
end

# maybe use expr_type?
function value_typ(ir::IRCode, value)
    isa(value, SSAValue) && return ir.types[value.id]
    isa(value, GlobalRef) && return abstract_eval_global(value.mod, value.name)
    isa(value, Argument) && return ir.argtypes[value.n]
    # TODO: isa QuoteNode, etc.
    return typeof(value)
end

function value_typ(ir::IncrementalCompact, value)
    isa(value, SSAValue) && return types(ir)[value.id]
    isa(value, GlobalRef) && return abstract_eval_global(value.mod, value.name)
    isa(value, Argument) && return ir.ir.argtypes[value.n]
    # TODO: isa QuoteNode, etc.
    return typeof(value)
end


start(compact::IncrementalCompact) = (compact.idx, 1)
function done(compact::IncrementalCompact, (idx, _a)::Tuple{Int, Int})
    return idx > length(compact.ir.stmts) && (compact.new_nodes_idx > length(compact.perm))
end

function process_phinode_values(old_values, late_fixup, processed_idx, result_idx, ssa_rename, used_ssas)
    values = Vector{Any}(undef, length(old_values))
    for i = 1:length(old_values)
        isassigned(old_values, i) || continue
        val = old_values[i]
        if isa(val, SSAValue)
            if val.id > processed_idx
                push!(late_fixup, result_idx)
                val = OldSSAValue(val.id)
            else
                val = renumber_ssa!(val, ssa_rename, true, used_ssas)
            end
        end
        values[i] = val
    end
    values
end

function process_node!(result::Vector{Any}, result_idx::Int, ssa_rename::Vector{Any},
        late_fixup::Vector{Int}, used_ssas::Vector{Int}, @nospecialize(stmt),
        idx::Int, processed_idx::Int)
    ssa_rename[idx] = SSAValue(result_idx)
    if stmt === nothing
        ssa_rename[idx] = stmt
    elseif isa(stmt, OldSSAValue)
        ssa_rename[idx] = ssa_rename[stmt.id]
    elseif isa(stmt, GotoNode) || isa(stmt, GlobalRef)
        result[result_idx] = stmt
        result_idx += 1
    elseif isa(stmt, Expr) || isa(stmt, PiNode) || isa(stmt, GotoIfNot) || isa(stmt, ReturnNode) || isa(stmt, UpsilonNode)
        result[result_idx] = renumber_ssa!(stmt, ssa_rename, true, used_ssas)
        result_idx += 1
    elseif isa(stmt, PhiNode)
        result[result_idx] = PhiNode(stmt.edges, process_phinode_values(stmt.values, late_fixup, processed_idx, result_idx, ssa_rename, used_ssas))
        result_idx += 1
    elseif isa(stmt, PhiCNode)
        result[result_idx] = PhiCNode(process_phinode_values(stmt.values, late_fixup, processed_idx, result_idx, ssa_rename, used_ssas))
        result_idx += 1
    elseif isa(stmt, SSAValue)
        # identity assign, replace uses of this ssa value with its result
        stmt = ssa_rename[stmt.id]
        ssa_rename[idx] = stmt
    else
        # Constant assign, replace uses of this ssa value with its result
        ssa_rename[idx] = stmt
    end
    return result_idx
end
function process_node!(compact::IncrementalCompact, result_idx::Int, @nospecialize(stmt), idx::Int, processed_idx::Int)
    return process_node!(compact.result, result_idx, compact.ssa_rename,
        compact.late_fixup, compact.used_ssas, stmt, idx, processed_idx)
end

function resize!(compact::IncrementalCompact, nnewnodes)
    old_length = length(compact.result)
    resize!(compact.result, nnewnodes)
    resize!(compact.result_types, nnewnodes)
    resize!(compact.result_lines, nnewnodes)
    resize!(compact.used_ssas, nnewnodes)
    compact.used_ssas[(old_length+1):nnewnodes] = 0
end

function finish_current_bb!(compact, old_result_idx=compact.result_idx)
    bb = compact.result_bbs[compact.active_result_bb]
    # If this was the last statement in the BB and we decided to skip it, insert a
    # dummy `nothing` node, to prevent changing the structure of the CFG
    if compact.result_idx == first(bb.stmts)
        length(compact.result) < old_result_idx && resize!(compact, old_result_idx)
        compact.result[old_result_idx] = nothing
        compact.result_types[old_result_idx] = Nothing
        compact.result_lines[old_result_idx] = 0
        compact.result_idx = old_result_idx + 1
    end
    compact.result_bbs[compact.active_result_bb] = BasicBlock(bb, StmtRange(first(bb.stmts), compact.result_idx-1))
    compact.active_result_bb += 1
    if compact.active_result_bb <= length(compact.result_bbs)
        new_bb = compact.result_bbs[compact.active_result_bb]
        compact.result_bbs[compact.active_result_bb] = BasicBlock(new_bb,
            StmtRange(compact.result_idx, last(new_bb.stmts)))
    end
end

function reverse_affinity_stmt_after(compact::IncrementalCompact, idx::Int)
    compact.new_nodes_idx > length(compact.perm) && return false
    entry = compact.ir.new_nodes[compact.perm[compact.new_nodes_idx]]
    entry.pos == idx && entry.reverse_affinity
end

function process_newnode!(compact, new_idx, new_node_entry, idx, active_bb)
    old_result_idx = compact.result_idx
    bb = compact.ir.cfg.blocks[active_bb]
    compact.result_types[old_result_idx] = new_node_entry.typ
    compact.result_lines[old_result_idx] = new_node_entry.line
    result_idx = process_node!(compact, old_result_idx, new_node_entry.node, new_idx, idx)
    compact.result_idx = result_idx
    # If this instruction has reverse affinity and we were at the end of a basic block,
    # finish it now.
    if new_node_entry.reverse_affinity && idx == last(bb.stmts)+1 && !reverse_affinity_stmt_after(compact, idx-1)
        active_bb += 1
        finish_current_bb!(compact, old_result_idx)
    end
    (old_result_idx == result_idx) && return next(compact, (idx, active_bb))
    return (old_result_idx, compact.result[old_result_idx]), (compact.idx, active_bb)
end

function next(compact::IncrementalCompact, (idx, active_bb)::Tuple{Int, Int})
    old_result_idx = compact.result_idx
    if length(compact.result) < old_result_idx
        resize!(compact, old_result_idx)
    end
    bb = compact.ir.cfg.blocks[active_bb]
    if compact.new_nodes_idx <= length(compact.perm) &&
        (entry =  compact.ir.new_nodes[compact.perm[compact.new_nodes_idx]];
         entry.reverse_affinity ? entry.pos == idx - 1 : entry.pos == idx)
        new_idx = compact.perm[compact.new_nodes_idx]
        compact.new_nodes_idx += 1
        new_node_entry = compact.ir.new_nodes[new_idx]
        new_idx += length(compact.ir.stmts)
        return process_newnode!(compact, new_idx, new_node_entry, idx, active_bb)
    elseif !isempty(compact.pending_perm) &&
        (entry = compact.pending_nodes[compact.pending_perm[1]];
         entry.reverse_affinity ? entry.pos == idx - 1 : entry.pos == idx)
        new_idx = popfirst!(compact.pending_perm)
        new_node_entry = compact.pending_nodes[new_idx]
        new_idx += length(compact.ir.stmts) + length(compact.ir.new_nodes)
        return process_newnode!(compact, new_idx, new_node_entry, idx, active_bb)
    end
    # This will get overwritten in future iterations if
    # result_idx is not, incremented, but that's ok and expected
    compact.result_types[old_result_idx] = compact.ir.types[idx]
    compact.result_lines[old_result_idx] = compact.ir.lines[idx]
    result_idx = process_node!(compact, old_result_idx, compact.ir.stmts[idx], idx, idx)
    stmt_if_any = old_result_idx == result_idx ? nothing : compact.result[old_result_idx]
    compact.result_idx = result_idx
    if idx == last(bb.stmts) && !reverse_affinity_stmt_after(compact, idx)
        active_bb += 1
        finish_current_bb!(compact, old_result_idx)
    end
    (old_result_idx == compact.result_idx) && return next(compact, (idx + 1, active_bb))
    compact.idx = idx + 1
    if !isassigned(compact.result, old_result_idx)
        @assert false
    end
    return (old_result_idx, compact.result[old_result_idx]), (compact.idx, active_bb)
end

function maybe_erase_unused!(extra_worklist, compact, idx, callback = x->nothing)
    stmt = compact.result[idx]
    stmt === nothing && return false
    effect_free = stmt_effect_free(stmt, compact, compact.ir.mod)
    if effect_free
        for ops in userefs(stmt)
            val = ops[]
            if isa(val, SSAValue)
                if compact.used_ssas[val.id] == 1
                    if val.id < idx
                        push!(extra_worklist, val.id)
                    end
                end
                compact.used_ssas[val.id] -= 1
                callback(val)
            end
        end
        compact.result[idx] = nothing
        return true
    end
    return false
end

function fixup_phinode_values!(compact, old_values)
    values = Vector{Any}(undef, length(old_values))
    for i = 1:length(old_values)
        isassigned(old_values, i) || continue
        val = old_values[i]
        if isa(val, OldSSAValue)
            val = compact.ssa_rename[val.id]
            if isa(val, SSAValue)
                compact.used_ssas[val.id] += 1
            end
        elseif isa(val, NewSSAValue)
            val = SSAValue(length(compact.result) + val.id)
        end
        values[i] = val
    end
    values
end

function fixup_node(compact, @nospecialize(stmt))
    if isa(stmt, PhiNode)
        return PhiNode(stmt.edges, fixup_phinode_values!(compact, stmt.values))
    elseif isa(stmt, PhiCNode)
        return PhiCNode(fixup_phinode_values!(compact, stmt.values))
    elseif isa(stmt, NewSSAValue)
        return SSAValue(length(compact.result) + stmt.id)
    else
        urs = userefs(stmt)
        urs === () && return stmt
        for ur in urs
            val = ur[]
            if isa(val, NewSSAValue)
                ur[] = SSAValue(length(compact.result) + val.id)
            end
        end
        return urs[]
    end
end

function just_fixup!(compact)
    for idx in compact.late_fixup
        stmt = compact.result[idx]
        new_stmt = fixup_node(compact, stmt)
        (stmt !== new_stmt) && (compact.result[idx] = new_stmt)
    end
    for idx in 1:length(compact.new_new_nodes)
        node = compact.new_new_nodes[idx]
        new_stmt = fixup_node(compact, node.node)
        (node.node !== new_stmt) && (compact.new_new_nodes[idx] = NewNode(node, node=new_stmt))
    end
end

function simple_dce!(compact)
    # Perform simple DCE for unused values
    extra_worklist = Int[]
    for (idx, nused) in Iterators.enumerate(compact.used_ssas)
        idx >= compact.result_idx && break
        nused == 0 || continue
        maybe_erase_unused!(extra_worklist, compact, idx)
    end
    while !isempty(extra_worklist)
        maybe_erase_unused!(extra_worklist, compact, pop!(extra_worklist))
    end
end

function non_dce_finish!(compact::IncrementalCompact)
    result_idx = compact.result_idx
    resize!(compact.result, result_idx-1)
    resize!(compact.result_types, result_idx-1)
    resize!(compact.result_lines, result_idx-1)
    just_fixup!(compact)
    bb = compact.result_bbs[end]
    compact.result_bbs[end] = BasicBlock(bb,
                StmtRange(first(bb.stmts), result_idx-1))
end

function finish(compact::IncrementalCompact)
    non_dce_finish!(compact)
    simple_dce!(compact)
    complete(compact)
end

function complete(compact)
    cfg = CFG(compact.result_bbs, Int[first(bb.stmts) for bb in compact.result_bbs[2:end]])
    return IRCode(compact.ir, compact.result, compact.result_types, compact.result_lines, cfg, compact.new_new_nodes)
end

function compact!(code::IRCode)
    compact = IncrementalCompact(code)
    # Just run through the iterator without any processing
    state = start(compact)
    while !done(compact, state)
        _, state = next(compact, state)
    end
    return finish(compact)
end

struct BBIdxStmt
    ir::IRCode
end

bbidxstmt(ir) = BBIdxStmt(ir)

start(x::BBIdxStmt) = (1,1)
done(x::BBIdxStmt, (idx, bb)) = idx > length(x.ir.stmts)
function next(x::BBIdxStmt, (idx, bb))
    active_bb = x.ir.cfg.blocks[bb]
    next_bb = bb
    if idx == last(active_bb.stmts)
        next_bb += 1
    end
    return (bb, idx, x.ir.stmts[idx]), (idx + 1, next_bb)
end

/*
*  Copyright (C) 2014 Nokia Corporation and/or its subsidiary(-ies).
*
* Redistribution and use in source and binary forms, with or without
* modification, are permitted provided that the following conditions
* are met:
* 1. Redistributions of source code must retain the above copyright
*    notice, this list of conditions and the following disclaimer.
* 2. Redistributions in binary form must reproduce the above copyright
*    notice, this list of conditions and the following disclaimer in the
*    documentation and/or other materials provided with the distribution.
*
* THIS SOFTWARE IS PROVIDED BY APPLE COMPUTER, INC. ``AS IS'' AND ANY
* EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
* IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
* PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL APPLE COMPUTER, INC. OR
* CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL,
* EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO,
* PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR
* PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY
* OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
* (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
* OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
*/

(function() {
    return (typeof window == "undefined" && typeof exports == "object") ? exports : window;
})().Statechart = (function() {

var FinalState = 'F', HistoryState = 'H', StandardState = 'S', ParallelState = 'P';
var OnState = "__on__", OffState = "__off__", RootState = "__root__", StartEvent = "__start__", StopEvent = "__stop__";

function uniqueAdd(array, item) { (array.indexOf(item) < 0 ? array : []).push(item); }
var argsToArray = Array;
function buildFromArgs(args, defaultFunc) {
    var obj = {};
    args.forEach(function(a) {
        switch (typeof(a)) {
        case "string": obj.id = a; break;
        case "function": obj[defaultFunc] = a; break;
        case "object":
            if (a.cls) {
                obj[a.cls] = obj[a.cls] || [];
                obj[a.cls].push(a.obj);
                break;
            }

            for (var n in a)
                obj[n] = a[n];
            break;
        }
    });
    return obj;
}

function buildState(type, args) {
    var state = buildFromArgs(args);
    var validAttribs = { };
    ["states", "onentry", "onexit", "initial", "deep", "transitions", "subcharts", "id", "exportEvents"]
        .forEach(function(a) {
            validAttribs[a] = true;
        });

    for (var prop in state) {
        if (!validAttribs[prop])
            throw new TypeError("Invalid state attribute: " + prop);
        validAttribs[prop] = false;
    }
    if (typeof(state.deep) !== "undefined" && type == HistoryState)
        throw new TypeError("Deep attribute only applies to history states");

    var props = { type: type, historyStates: [], states: state.states || [], transitions: state.transitions || [] };
    for (var n in props)
        state[n] = props[n];
    state.atomic = (state.type !== HistoryState && !(state.states || []).length);

    state.states.forEach(function(s) {
        s.parent = state;
        state.initialState = (s.initial || !state.initialState ? s : state.initialState);
        (s.type == HistoryState ? state.historyStates : []).push(s);
    });

    state.subcharts = (state.subcharts || []).map(function(subchart) {
        var sc;
        (subchart.obj.exportEvents || []).forEach(function(e) {
            subchart.obj.transitions.push({ source: subchart.obj, event: e, ontrigger: function(event) { state.emit(event); } });
            state.transitions.push({ event: e, ontrigger: function(event) { sc.emit(event); } });
        });
        var wrappedSpec =
            Sugar.State(RootState,
                Sugar.State(OnState, spec, Sugar.Transition(Sugar.Event(StopEvent), Sugar.Target(OffState))),
                Sugar.State(OffState, Sugar.Initial, Sugar.Transition(Sugar.Event(StartEvent), Sugar.Target(OnState)))
            );
        sc = new StatechartPrivate(wrappedSpec);
        sc.stop = function() { sc.emit({ name: StopEvent }); };
        sc.start = function() { sc.emit({ name: StartEvent }); };
        return sc;
    });

    state.transitions.forEach(function(t) { t.source = state; });
    return { cls: "states", obj: state };
}

function validateTransition(t) {
    var validAttribs = ["event", "condition", "ontrigger", "targets"];
    for (var n in t.obj) {
        if (!validAttribs.splice(validAttribs.indexOf(n), 1))
            throw new TypeError("Illegal transition attribute: " + n);
    }

    if (!t.obj.targets && !t.obj.ontrigger)
        throw new TypeError("Transition has no side effects");

    return t;
}

function isDescendant(child, potentialAncestor) {
    for (var ancestor = (child || {}).parent; ancestor; ancestor = ancestor.parent) {
        if (ancestor === potentialAncestor)
            return true;
    }
    return false;
}

function getProperAncestors(state, root) {
    var ancs = [];
    for (var s = (state || {}).parent; s !== root && s; s = s.parent)
        ancs.push(s);
    return ancs;
}

function entryOrder(a, b) { return a.sortIndex - b.sortIndex; }
function eventMatch(e1, e2) { return (e1 === e2) || (e2 && e1 === "*"); }

function build(rootSpec) {
    var stateByID = {},
        externalQueue = [],
        internalQueue = [],
        processing = false,
        historyValues = {},
        configuration = [],
        internalEmitter = {},
        event = { name: "", data: { } },
        doContinue = false,
        nextStateIndex = 0,
        rootState = rootSpec.obj;

    function emitInternal(e) {
        if (processing)
            internalQueue.push(e);
        else
            emitExternal(e);
    }

    function emitExternal(e) {
        externalQueue.push(e);
        process();
    }

    function visitState(state) {
        state.sortIndex = nextStateIndex++;
        state.emit = emitExternal;
        if (stateByID[state.id])
            throw new TypeError("State " + state.id + " already exists");
        stateByID[state.id] = state;
    }

    function resolveTransitions(state) {
        (state.transitions || []).forEach(function(t) {
            if (t.event && t.event.length && t.event !== "*")
                internalEmitter[t.event] = function(payload) {
                    emitInternal({ name: t.event, data: payload });
                };

            t.targets = (t.targets || []).map(function(e) {
                var state = stateByID[e];
                if (!state)
                    throw new TypeError("State " + e + " not found, in transition from state " + state.id);
                return state;
            });
        });
    }

    function walkStateTree(root, visitor) {
        visitor(root);
        (root.states || []).forEach(function(s) {
            visit(s, visitor);
        });
    }

    if (!rootState.states || !rootState.states.length)
        throw new TypeError("The root state has to have at least one child state.");

    walkStateTree(rootState, visitState);
    walkStateTree(rootState, resolveTransitions);

    function findLCA(source, targets) {
        var lca;
        var sourceAncestors = getProperAncestors(source);
        return sourceAncestors.some(function(ancestor) {
            if (!targets.some(function(target) {
                return !isDescendant(target, ancestor);
            })) {
                return false;
            }
            lca = anc;
            return true;
        }) ? lca : rootState;
    }

    function isPreempted(state, transitions) {
        return transitions.some(function(t) {
            return (t.targets || []).length && isDescendant(state, findLCA(t.source, t.targets));
        });
    }

    function isInFinalState(state) {
        switch (state.type) {
        case FinalState:
            return true;
        case StandardState:
            return configuration.some(function(s) { return s.parent == state && s.type == FinalState; });
        case ParallelState:
            return !state.states.some(function(s) { return !isInFinalState(s); });
        default:
            return false;
        }
    }

    function addStatesToEnter(s, root, statesToEnter) {
        if (s.type === HistoryState) {
            var h = historyValues[s.id];
            if (h) {
                h.forEach(function(state) { addStatesToEnter(state, root, statesToEnter); });
                return;
            }

            if (s.states.length)
                addStatesToEnter(s.initialState, s, statesToEnter);

            return;
        }

        uniqueAdd(statesToEnter, s);

        if (s.type === ParallelState)
            s.states.forEach(function(state) { addStatesToEnter(state, s, statesToEnter); });

        if (s.type === StandardState && s.states.length)
            addStatesToEnter(s.initialState || s.states[0], s, statesToEnter);

        var properAncestors = getProperAncestors(s, root);
        if ((root || {}).type === ParallelState)
            properAncestors.splice(properAncestors.length, 0, root.states);

        properAncestors.forEach(function(anc) {
            uniqueAdd(statesToEnter, anc);
            (anc.type === ParallelState ? (anc.states || []) : []).forEach(function(child) {
                if (!statesToEnter.some(function(state) {
                    return isDescendant(state, child);
                })) {
                    addStatesToEnter(child, anc, statesToEnter);
                }
            });
        });
    }

    function func(f, e) {
        if (f)
            f(e, internalEmitter);
    }

    function microstep(enabledTransitions) {
        exitStates(enabledTransitions);
        enabledTransitions.forEach(function(t) {
            func((t || {}).ontrigger, event);
        });
        enterStates(enabledTransitions);
    }

    function start() {
        doContinue = processing = true;
        rootState.parent = undefined;
        configuration = [];
        enterStates([{ source: rootState, targets: [rootState.initialState] }]);
        processing = true;
        var enabledTransitions = [];
        do {
            enabledTransitions = selectTransitions();
            while (!enabledTransitions.length && internalQueue.length)
                enabledTransitions = selectTransitions(event = internalQueue.shift());

            microstep(enabledTransitions);
        } while (enabledTransitions.length);
        processing = false;
        process();
    }

    function exitStates(enabledTransitions) {
        var statesToExit = [];
        (enabledTransitions || []).filter(function(t) { return (t.targets||[]).length; }).forEach(function (t) {
            var lca = findLCA(t.source, t.targets);
            configuration.filter(function(s) { return isDescendant(s, lca); }).forEach(function(s) {
                uniqueAdd(statesToExit, s);
            });
        });

        statesToExit = statesToExit.sort(entryOrder).reverse();
        statesToExit.forEach(function(s) {
            (s.historyStates || []).forEach(function(h) {
                historyValues[h.id] = configuration.filter(function(cur) {
                    return h.deep ? isDescendant(cur, s) : cur.parent === s;
                });
            });
        });

        statesToExit.forEach(function(s) {
            func(s.onexit, event);
            configuration = configuration.splice(configuration.indexOf(s), 1);
            (s.subcharts || []).forEach(function(sc) {
                sc.stop();
            });
        });
    }

    function enterStates(enabledTransitions) {
        var statesToEnter = [], statesForDefaultEntry = [];
        enabledTransitions.forEach(function(t) {
            var lca = findLCA(t.source, t.targets);
            (t.targets || []).forEach(function(target) {
                addStatesToEnter(target, lca, statesToEnter, statesForDefaultEntry);
            });
        });

        statesToEnter.sort(entryOrder).forEach(function(s) {
            uniqueAdd(configuration, s);
            func(s.onentry, event);
            (s.subcharts || []).forEach(function(sc) { sc.start(); });

            if (s.type === FinalState)
                [s.parent, s.parent.parent].forEach(function(s) { if (s && isInFinalState(s)) { emitInternal({ name: "done." + s.id }); } });
            doContinue = doContinue && !isInFinalState(rootState);
        });
    }

    function process() {
        if (processing)
            return;

        processing = true;
        while (externalQueue.length) {
            event = externalQueue.shift();
            var enabledTransitions = selectTransitions(event);

            if (!enabledTransitions.length)
                continue;

            microstep(enabledTransitions);

            do {
                for (enabledTransitions = selectTransitions(); !enabledTransitions.length;) {
                    event = internalQueue.shift();
                    if (!event)
                        break;
                    enabledTransitions = selectTransitions(event);
                }
                if (enabledTransitions.length)
                    microstep(enabledTransitions);
            } while (enabledTransitions.length);
        }

        processing = false;
    }

    function selectTransitions(e) {
        var enabledTransitions = [];
        configuration.filter(function(state) {
            return state.atomic && !isPreempted(state, enabledTransitions);
        }).forEach(function(state) {
            var ancs = [state].concat(getProperAncestors(state));
            ancs.filter(function(anc) { return anc.transitions; }).some(function(anc) {
                return anc.transitions.some(function(t) {
                    if (!(eventMatch(t.event, (e||{}).name)) || !(t.condition || function(){ return true; })(e))
                        return false;

                    uniqueAdd(enabledTransitions, t);
                    return true;
                });
            });
        });
        return enabledTransitions;
    }

    start();
    return emitExternal;
}

function StatechartPrivate(spec) {
    this.emit = build(spec);
}

var Statechart = function (spec) {
    var emit = build(spec);
    var self = this;
    (spec.obj.exportEvents || []).forEach(function(event) {
        var f = function(data) {
            emit({ name: event, data: data });
        };
        self[event] = f;
    });
};

(function(sugar) {
    for (var n in sugar) { Statechart[n] = sugar[n]; }
})({
    Entry: function (f) { return { onentry: f }; },
    Exit: function (f) { return { onexit: f }; },
    Event: function (e) { return { event: e }; },
    Export: function() { return { exportEvents: argsToArray.apply(null, arguments) }; },
    Condition: function (f) { return { condition: f }; },
    DataEquals: function(d) { return { condition: function(e) { return e.data === d; } }; },
    DataNotEquals: function(d) { return { condition: function(e) { return e.data !== d; } }; },
    Target: function (s) { return { targets: [s] }; },
    Initial: { initial: true },
    Deep: { deep: true },
    Final: function () { return buildState(FinalState, argsToArray.apply(null, arguments)); },
    State: function () { return buildState(StandardState, argsToArray.apply(null, arguments)); },
    Subchart: function(spec) { return { cls: "subcharts", obj: spec }; },
    Parallel: function () { return buildState(ParallelState, argsToArray.apply(null, arguments)); },
    History: function () { return buildState(HistoryState, argsToArray.apply(null, arguments)); },
    Targets: function () { return { targets: argsToArray.apply(null, arguments) }; },
    Transition: function () { return validateTransition({ cls: "transitions", obj: buildFromArgs(argsToArray.apply(null, arguments), "ontrigger") }); },
});
return Statechart;
})();
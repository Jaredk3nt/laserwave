// Copyright 2012 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

#include "src/api.h"

#include <string.h>  // For memcpy, strlen.
#include <cmath>     // For isnan.
#include <limits>
#include <vector>

#include "src/api-inl.h"

#include "include/v8-profiler.h"
#include "include/v8-testing.h"
#include "include/v8-util.h"
#include "src/accessors.h"
#include "src/api-natives.h"
#include "src/assert-scope.h"
#include "src/base/functional.h"
#include "src/base/logging.h"
#include "src/base/platform/platform.h"
#include "src/base/platform/time.h"
#include "src/base/safe_conversions.h"
#include "src/base/utils/random-number-generator.h"
#include "src/bootstrapper.h"
#include "src/builtins/builtins-utils.h"
#include "src/char-predicates-inl.h"
#include "src/code-stubs.h"
#include "src/compiler-dispatcher/compiler-dispatcher.h"
#include "src/compiler.h"
#include "src/contexts.h"
#include "src/conversions-inl.h"
#include "src/counters.h"
#include "src/debug/debug-coverage.h"
#include "src/debug/debug-evaluate.h"
#include "src/debug/debug-type-profile.h"
#include "src/debug/debug.h"
#include "src/debug/liveedit.h"
#include "src/deoptimizer.h"
#include "src/detachable-vector.h"
#include "src/execution.h"
#include "src/frames-inl.h"
#include "src/gdb-jit.h"
#include "src/global-handles.h"
#include "src/globals.h"
#include "src/icu_util.h"
#include "src/isolate-inl.h"
#include "src/json-parser.h"
#include "src/json-stringifier.h"
#include "src/messages.h"
#include "src/objects-inl.h"
#include "src/objects/api-callbacks.h"
#include "src/objects/js-array-inl.h"
#include "src/objects/js-collection-inl.h"
#include "src/objects/js-generator-inl.h"
#include "src/objects/js-promise-inl.h"
#include "src/objects/js-regexp-inl.h"
#include "src/objects/module-inl.h"
#include "src/objects/ordered-hash-table-inl.h"
#include "src/objects/slots.h"
#include "src/objects/stack-frame-info-inl.h"
#include "src/objects/templates.h"
#include "src/parsing/parse-info.h"
#include "src/parsing/parser.h"
#include "src/parsing/scanner-character-streams.h"
#include "src/pending-compilation-error-handler.h"
#include "src/profiler/cpu-profiler.h"
#include "src/profiler/heap-profiler.h"
#include "src/profiler/heap-snapshot-generator-inl.h"
#include "src/profiler/profile-generator-inl.h"
#include "src/profiler/tick-sample.h"
#include "src/property-descriptor.h"
#include "src/property-details.h"
#include "src/property.h"
#include "src/prototype.h"
#include "src/runtime-profiler.h"
#include "src/runtime/runtime.h"
#include "src/simulator.h"
#include "src/snapshot/builtin-serializer.h"
#include "src/snapshot/code-serializer.h"
#include "src/snapshot/natives.h"
#include "src/snapshot/partial-serializer.h"
#include "src/snapshot/read-only-serializer.h"
#include "src/snapshot/snapshot.h"
#include "src/snapshot/startup-serializer.h"
#include "src/startup-data-util.h"
#include "src/string-hasher.h"
#include "src/tracing/trace-event.h"
#include "src/trap-handler/trap-handler.h"
#include "src/unicode-cache-inl.h"
#include "src/unicode-inl.h"
#include "src/v8.h"
#include "src/v8threads.h"
#include "src/value-serializer.h"
#include "src/version.h"
#include "src/vm-state-inl.h"
#include "src/wasm/streaming-decoder.h"
#include "src/wasm/wasm-engine.h"
#include "src/wasm/wasm-objects-inl.h"
#include "src/wasm/wasm-result.h"
#include "src/wasm/wasm-serialization.h"

namespace v8 {

/*
 * Most API methods should use one of the three macros:
 *
 * ENTER_V8, ENTER_V8_NO_SCRIPT, ENTER_V8_NO_SCRIPT_NO_EXCEPTION.
 *
 * The latter two assume that no script is executed, and no exceptions are
 * scheduled in addition (respectively). Creating a pending exception and
 * removing it before returning is ok.
 *
 * Exceptions should be handled either by invoking one of the
 * RETURN_ON_FAILED_EXECUTION* macros.
 *
 * Don't use macros with DO_NOT_USE in their name.
 *
 * TODO(jochen): Document debugger specific macros.
 * TODO(jochen): Document LOG_API and other RuntimeCallStats macros.
 * TODO(jochen): All API methods should invoke one of the ENTER_V8* macros.
 * TODO(jochen): Remove calls form API methods to DO_NOT_USE macros.
 */

#define LOG_API(isolate, class_name, function_name)                           \
  i::RuntimeCallTimerScope _runtime_timer(                                    \
      isolate, i::RuntimeCallCounterId::kAPI_##class_name##_##function_name); \
  LOG(isolate, ApiEntryCall("v8::" #class_name "::" #function_name))

#define ENTER_V8_DO_NOT_USE(isolate) i::VMState<v8::OTHER> __state__((isolate))

#define ENTER_V8_HELPER_DO_NOT_USE(isolate, context, class_name,  \
                                   function_name, bailout_value,  \
                                   HandleScopeClass, do_callback) \
  if (IsExecutionTerminatingCheck(isolate)) {                     \
    return bailout_value;                                         \
  }                                                               \
  HandleScopeClass handle_scope(isolate);                         \
  CallDepthScope<do_callback> call_depth_scope(isolate, context); \
  LOG_API(isolate, class_name, function_name);                    \
  i::VMState<v8::OTHER> __state__((isolate));                     \
  bool has_pending_exception = false

#define PREPARE_FOR_DEBUG_INTERFACE_EXECUTION_WITH_ISOLATE(isolate, T)       \
  if (IsExecutionTerminatingCheck(isolate)) {                                \
    return MaybeLocal<T>();                                                  \
  }                                                                          \
  InternalEscapableScope handle_scope(isolate);                              \
  CallDepthScope<false> call_depth_scope(isolate, v8::Local<v8::Context>()); \
  i::VMState<v8::OTHER> __state__((isolate));                                \
  bool has_pending_exception = false

#define PREPARE_FOR_EXECUTION_WITH_CONTEXT(context, class_name, function_name, \
                                           bailout_value, HandleScopeClass,    \
                                           do_callback)                        \
  auto isolate = context.IsEmpty()                                             \
                     ? i::Isolate::Current()                                   \
                     : reinterpret_cast<i::Isolate*>(context->GetIsolate());   \
  ENTER_V8_HELPER_DO_NOT_USE(isolate, context, class_name, function_name,      \
                             bailout_value, HandleScopeClass, do_callback);

#define PREPARE_FOR_EXECUTION(context, class_name, function_name, T)          \
  PREPARE_FOR_EXECUTION_WITH_CONTEXT(context, class_name, function_name,      \
                                     MaybeLocal<T>(), InternalEscapableScope, \
                                     false)

#define ENTER_V8(isolate, context, class_name, function_name, bailout_value, \
                 HandleScopeClass)                                           \
  ENTER_V8_HELPER_DO_NOT_USE(isolate, context, class_name, function_name,    \
                             bailout_value, HandleScopeClass, true)

#ifdef DEBUG
#define ENTER_V8_NO_SCRIPT(isolate, context, class_name, function_name,   \
                           bailout_value, HandleScopeClass)               \
  ENTER_V8_HELPER_DO_NOT_USE(isolate, context, class_name, function_name, \
                             bailout_value, HandleScopeClass, false);     \
  i::DisallowJavascriptExecutionDebugOnly __no_script__((isolate))

#define ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate)                    \
  i::VMState<v8::OTHER> __state__((isolate));                       \
  i::DisallowJavascriptExecutionDebugOnly __no_script__((isolate)); \
  i::DisallowExceptions __no_exceptions__((isolate))

#define ENTER_V8_FOR_NEW_CONTEXT(isolate)     \
  i::VMState<v8::OTHER> __state__((isolate)); \
  i::DisallowExceptions __no_exceptions__((isolate))
#else
#define ENTER_V8_NO_SCRIPT(isolate, context, class_name, function_name,   \
                           bailout_value, HandleScopeClass)               \
  ENTER_V8_HELPER_DO_NOT_USE(isolate, context, class_name, function_name, \
                             bailout_value, HandleScopeClass, false)

#define ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate) \
  i::VMState<v8::OTHER> __state__((isolate));

#define ENTER_V8_FOR_NEW_CONTEXT(isolate) \
  i::VMState<v8::OTHER> __state__((isolate));
#endif  // DEBUG

#define EXCEPTION_BAILOUT_CHECK_SCOPED_DO_NOT_USE(isolate, value) \
  do {                                                            \
    if (has_pending_exception) {                                  \
      call_depth_scope.Escape();                                  \
      return value;                                               \
    }                                                             \
  } while (false)

#define RETURN_ON_FAILED_EXECUTION(T) \
  EXCEPTION_BAILOUT_CHECK_SCOPED_DO_NOT_USE(isolate, MaybeLocal<T>())

#define RETURN_ON_FAILED_EXECUTION_PRIMITIVE(T) \
  EXCEPTION_BAILOUT_CHECK_SCOPED_DO_NOT_USE(isolate, Nothing<T>())

#define RETURN_TO_LOCAL_UNCHECKED(maybe_local, T) \
  return maybe_local.FromMaybe(Local<T>());


#define RETURN_ESCAPED(value) return handle_scope.Escape(value);

namespace {

Local<Context> ContextFromNeverReadOnlySpaceObject(
    i::Handle<i::NeverReadOnlySpaceObject> obj) {
  return reinterpret_cast<v8::Isolate*>(obj->GetIsolate())->GetCurrentContext();
}

class InternalEscapableScope : public v8::EscapableHandleScope {
 public:
  explicit inline InternalEscapableScope(i::Isolate* isolate)
      : v8::EscapableHandleScope(reinterpret_cast<v8::Isolate*>(isolate)) {}
};

// TODO(jochen): This should be #ifdef DEBUG
#ifdef V8_CHECK_MICROTASKS_SCOPES_CONSISTENCY
void CheckMicrotasksScopesConsistency(i::Isolate* isolate) {
  auto handle_scope_implementer = isolate->handle_scope_implementer();
  if (handle_scope_implementer->microtasks_policy() ==
      v8::MicrotasksPolicy::kScoped) {
    DCHECK(handle_scope_implementer->GetMicrotasksScopeDepth() ||
           !handle_scope_implementer->DebugMicrotasksScopeDepthIsZero());
  }
}
#endif

template <bool do_callback>
class CallDepthScope {
 public:
  explicit CallDepthScope(i::Isolate* isolate, Local<Context> context)
      : isolate_(isolate),
        context_(context),
        escaped_(false),
        safe_for_termination_(isolate->next_v8_call_is_safe_for_termination()),
        interrupts_scope_(isolate_, i::StackGuard::TERMINATE_EXECUTION,
                          isolate_->only_terminate_in_safe_scope()
                              ? (safe_for_termination_
                                     ? i::InterruptsScope::kRunInterrupts
                                     : i::InterruptsScope::kPostponeInterrupts)
                              : i::InterruptsScope::kNoop) {
    // TODO(dcarney): remove this when blink stops crashing.
    DCHECK(!isolate_->external_caught_exception());
    isolate_->handle_scope_implementer()->IncrementCallDepth();
    isolate_->set_next_v8_call_is_safe_for_termination(false);
    if (!context.IsEmpty()) {
      i::Handle<i::Context> env = Utils::OpenHandle(*context);
      i::HandleScopeImplementer* impl = isolate->handle_scope_implementer();
      if (isolate->context() != nullptr &&
          isolate->context()->native_context() == env->native_context()) {
        context_ = Local<Context>();
      } else {
        impl->SaveContext(isolate->context());
        isolate->set_context(*env);
      }
    }
    if (do_callback) isolate_->FireBeforeCallEnteredCallback();
  }
  ~CallDepthScope() {
    if (!context_.IsEmpty()) {
      i::HandleScopeImplementer* impl = isolate_->handle_scope_implementer();
      isolate_->set_context(impl->RestoreContext());
    }
    if (!escaped_) isolate_->handle_scope_implementer()->DecrementCallDepth();
    if (do_callback) isolate_->FireCallCompletedCallback();
// TODO(jochen): This should be #ifdef DEBUG
#ifdef V8_CHECK_MICROTASKS_SCOPES_CONSISTENCY
    if (do_callback) CheckMicrotasksScopesConsistency(isolate_);
#endif
    isolate_->set_next_v8_call_is_safe_for_termination(safe_for_termination_);
  }

  void Escape() {
    DCHECK(!escaped_);
    escaped_ = true;
    auto handle_scope_implementer = isolate_->handle_scope_implementer();
    handle_scope_implementer->DecrementCallDepth();
    bool call_depth_is_zero = handle_scope_implementer->CallDepthIsZero();
    isolate_->OptionalRescheduleException(call_depth_is_zero);
  }

 private:
  i::Isolate* const isolate_;
  Local<Context> context_;
  bool escaped_;
  bool do_callback_;
  bool safe_for_termination_;
  i::InterruptsScope interrupts_scope_;
};

}  // namespace


static ScriptOrigin GetScriptOriginForScript(i::Isolate* isolate,
                                             i::Handle<i::Script> script) {
  i::Handle<i::Object> scriptName(script->GetNameOrSourceURL(), isolate);
  i::Handle<i::Object> source_map_url(script->source_mapping_url(), isolate);
  i::Handle<i::FixedArray> host_defined_options(script->host_defined_options(),
                                                isolate);
  v8::Isolate* v8_isolate = reinterpret_cast<v8::Isolate*>(isolate);
  ScriptOriginOptions options(script->origin_options());
  v8::ScriptOrigin origin(
      Utils::ToLocal(scriptName),
      v8::Integer::New(v8_isolate, script->line_offset()),
      v8::Integer::New(v8_isolate, script->column_offset()),
      v8::Boolean::New(v8_isolate, options.IsSharedCrossOrigin()),
      v8::Integer::New(v8_isolate, script->id()),
      Utils::ToLocal(source_map_url),
      v8::Boolean::New(v8_isolate, options.IsOpaque()),
      v8::Boolean::New(v8_isolate, script->type() == i::Script::TYPE_WASM),
      v8::Boolean::New(v8_isolate, options.IsModule()),
      Utils::ToLocal(host_defined_options));
  return origin;
}


// --- E x c e p t i o n   B e h a v i o r ---

void i::FatalProcessOutOfMemory(i::Isolate* isolate, const char* location) {
  i::V8::FatalProcessOutOfMemory(isolate, location, false);
}

// When V8 cannot allocate memory FatalProcessOutOfMemory is called. The default
// OOM error handler is called and execution is stopped.
void i::V8::FatalProcessOutOfMemory(i::Isolate* isolate, const char* location,
                                    bool is_heap_oom) {
  char last_few_messages[Heap::kTraceRingBufferSize + 1];
  char js_stacktrace[Heap::kStacktraceBufferSize + 1];
  i::HeapStats heap_stats;

  if (isolate == nullptr) {
    isolate = Isolate::Current();
  }

  if (isolate == nullptr) {
    // On a background thread -> we cannot retrieve memory information from the
    // Isolate. Write easy-to-recognize values on the stack.
    memset(last_few_messages, 0x0BADC0DE, Heap::kTraceRingBufferSize + 1);
    memset(js_stacktrace, 0x0BADC0DE, Heap::kStacktraceBufferSize + 1);
    memset(&heap_stats, 0xBADC0DE, sizeof(heap_stats));
    // Note that the embedder's oom handler won't be called in this case. We
    // just crash.
    FATAL(
        "API fatal error handler returned after process out of memory on the "
        "background thread");
    UNREACHABLE();
  }

  memset(last_few_messages, 0, Heap::kTraceRingBufferSize + 1);
  memset(js_stacktrace, 0, Heap::kStacktraceBufferSize + 1);

  intptr_t start_marker;
  heap_stats.start_marker = &start_marker;
  size_t ro_space_size;
  heap_stats.ro_space_size = &ro_space_size;
  size_t ro_space_capacity;
  heap_stats.ro_space_capacity = &ro_space_capacity;
  size_t new_space_size;
  heap_stats.new_space_size = &new_space_size;
  size_t new_space_capacity;
  heap_stats.new_space_capacity = &new_space_capacity;
  size_t old_space_size;
  heap_stats.old_space_size = &old_space_size;
  size_t old_space_capacity;
  heap_stats.old_space_capacity = &old_space_capacity;
  size_t code_space_size;
  heap_stats.code_space_size = &code_space_size;
  size_t code_space_capacity;
  heap_stats.code_space_capacity = &code_space_capacity;
  size_t map_space_size;
  heap_stats.map_space_size = &map_space_size;
  size_t map_space_capacity;
  heap_stats.map_space_capacity = &map_space_capacity;
  size_t lo_space_size;
  heap_stats.lo_space_size = &lo_space_size;
  size_t global_handle_count;
  heap_stats.global_handle_count = &global_handle_count;
  size_t weak_global_handle_count;
  heap_stats.weak_global_handle_count = &weak_global_handle_count;
  size_t pending_global_handle_count;
  heap_stats.pending_global_handle_count = &pending_global_handle_count;
  size_t near_death_global_handle_count;
  heap_stats.near_death_global_handle_count = &near_death_global_handle_count;
  size_t free_global_handle_count;
  heap_stats.free_global_handle_count = &free_global_handle_count;
  size_t memory_allocator_size;
  heap_stats.memory_allocator_size = &memory_allocator_size;
  size_t memory_allocator_capacity;
  heap_stats.memory_allocator_capacity = &memory_allocator_capacity;
  size_t malloced_memory;
  heap_stats.malloced_memory = &malloced_memory;
  size_t malloced_peak_memory;
  heap_stats.malloced_peak_memory = &malloced_peak_memory;
  size_t objects_per_type[LAST_TYPE + 1] = {0};
  heap_stats.objects_per_type = objects_per_type;
  size_t size_per_type[LAST_TYPE + 1] = {0};
  heap_stats.size_per_type = size_per_type;
  int os_error;
  heap_stats.os_error = &os_error;
  heap_stats.last_few_messages = last_few_messages;
  heap_stats.js_stacktrace = js_stacktrace;
  intptr_t end_marker;
  heap_stats.end_marker = &end_marker;
  if (isolate->heap()->HasBeenSetUp()) {
    // BUG(1718): Don't use the take_snapshot since we don't support
    // HeapIterator here without doing a special GC.
    isolate->heap()->RecordStats(&heap_stats, false);
    char* first_newline = strchr(last_few_messages, '\n');
    if (first_newline == nullptr || first_newline[1] == '\0')
      first_newline = last_few_messages;
    PrintF("\n<--- Last few GCs --->\n%s\n", first_newline);
    PrintF("\n<--- JS stacktrace --->\n%s\n", js_stacktrace);
  }
  Utils::ReportOOMFailure(isolate, location, is_heap_oom);
  // If the fatal error handler returns, we stop execution.
  FATAL("API fatal error handler returned after process out of memory");
}


void Utils::ReportApiFailure(const char* location, const char* message) {
  i::Isolate* isolate = i::Isolate::Current();
  FatalErrorCallback callback = nullptr;
  if (isolate != nullptr) {
    callback = isolate->exception_behavior();
  }
  if (callback == nullptr) {
    base::OS::PrintError("\n#\n# Fatal error in %s\n# %s\n#\n\n", location,
                         message);
    base::OS::Abort();
  } else {
    callback(location, message);
  }
  isolate->SignalFatalError();
}

void Utils::ReportOOMFailure(i::Isolate* isolate, const char* location,
                             bool is_heap_oom) {
  OOMErrorCallback oom_callback = isolate->oom_behavior();
  if (oom_callback == nullptr) {
    // TODO(wfh): Remove this fallback once Blink is setting OOM handler. See
    // crbug.com/614440.
    FatalErrorCallback fatal_callback = isolate->exception_behavior();
    if (fatal_callback == nullptr) {
      base::OS::PrintError("\n#\n# Fatal %s OOM in %s\n#\n\n",
                           is_heap_oom ? "javascript" : "process", location);
      base::OS::Abort();
    } else {
      fatal_callback(location,
                     is_heap_oom
                         ? "Allocation failed - JavaScript heap out of memory"
                         : "Allocation failed - process out of memory");
    }
  } else {
    oom_callback(location, is_heap_oom);
  }
  isolate->SignalFatalError();
}

static inline bool IsExecutionTerminatingCheck(i::Isolate* isolate) {
  if (isolate->has_scheduled_exception()) {
    return isolate->scheduled_exception() ==
           i::ReadOnlyRoots(isolate).termination_exception();
  }
  return false;
}


void V8::SetNativesDataBlob(StartupData* natives_blob) {
  i::V8::SetNativesBlob(natives_blob);
}


void V8::SetSnapshotDataBlob(StartupData* snapshot_blob) {
  i::V8::SetSnapshotBlob(snapshot_blob);
}

namespace {

class ArrayBufferAllocator : public v8::ArrayBuffer::Allocator {
 public:
  void* Allocate(size_t length) override {
#if V8_OS_AIX && _LINUX_SOURCE_COMPAT
    // Work around for GCC bug on AIX
    // See: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=79839
    void* data = __linux_calloc(length, 1);
#else
    void* data = calloc(length, 1);
#endif
    return data;
  }

  void* AllocateUninitialized(size_t length) override {
#if V8_OS_AIX && _LINUX_SOURCE_COMPAT
    // Work around for GCC bug on AIX
    // See: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=79839
    void* data = __linux_malloc(length);
#else
    void* data = malloc(length);
#endif
    return data;
  }

  void Free(void* data, size_t) override { free(data); }
};

struct SnapshotCreatorData {
  explicit SnapshotCreatorData(Isolate* isolate)
      : isolate_(isolate),
        default_context_(),
        contexts_(isolate),
        created_(false) {}

  static SnapshotCreatorData* cast(void* data) {
    return reinterpret_cast<SnapshotCreatorData*>(data);
  }

  ArrayBufferAllocator allocator_;
  Isolate* isolate_;
  Persistent<Context> default_context_;
  SerializeInternalFieldsCallback default_embedder_fields_serializer_;
  PersistentValueVector<Context> contexts_;
  std::vector<SerializeInternalFieldsCallback> embedder_fields_serializers_;
  bool created_;
};

}  // namespace

SnapshotCreator::SnapshotCreator(Isolate* isolate,
                                 const intptr_t* external_references,
                                 StartupData* existing_snapshot) {
  SnapshotCreatorData* data = new SnapshotCreatorData(isolate);
  data->isolate_ = isolate;
  i::Isolate* internal_isolate = reinterpret_cast<i::Isolate*>(isolate);
  internal_isolate->set_array_buffer_allocator(&data->allocator_);
  internal_isolate->set_api_external_references(external_references);
  internal_isolate->enable_serializer();
  isolate->Enter();
  const StartupData* blob = existing_snapshot
                                ? existing_snapshot
                                : i::Snapshot::DefaultSnapshotBlob();
  if (blob && blob->raw_size > 0) {
    internal_isolate->set_snapshot_blob(blob);
    i::Snapshot::Initialize(internal_isolate);
  } else {
    internal_isolate->Init(nullptr);
  }
  data_ = data;
}

SnapshotCreator::SnapshotCreator(const intptr_t* external_references,
                                 StartupData* existing_snapshot)
    : SnapshotCreator(reinterpret_cast<Isolate*>(new i::Isolate()),
                      external_references, existing_snapshot) {}

SnapshotCreator::~SnapshotCreator() {
  SnapshotCreatorData* data = SnapshotCreatorData::cast(data_);
  DCHECK(data->created_);
  Isolate* isolate = data->isolate_;
  isolate->Exit();
  isolate->Dispose();
  delete data;
}

Isolate* SnapshotCreator::GetIsolate() {
  return SnapshotCreatorData::cast(data_)->isolate_;
}

void SnapshotCreator::SetDefaultContext(
    Local<Context> context, SerializeInternalFieldsCallback callback) {
  DCHECK(!context.IsEmpty());
  SnapshotCreatorData* data = SnapshotCreatorData::cast(data_);
  DCHECK(!data->created_);
  DCHECK(data->default_context_.IsEmpty());
  Isolate* isolate = data->isolate_;
  CHECK_EQ(isolate, context->GetIsolate());
  data->default_context_.Reset(isolate, context);
  data->default_embedder_fields_serializer_ = callback;
}

size_t SnapshotCreator::AddContext(Local<Context> context,
                                   SerializeInternalFieldsCallback callback) {
  DCHECK(!context.IsEmpty());
  SnapshotCreatorData* data = SnapshotCreatorData::cast(data_);
  DCHECK(!data->created_);
  Isolate* isolate = data->isolate_;
  CHECK_EQ(isolate, context->GetIsolate());
  size_t index = data->contexts_.Size();
  data->contexts_.Append(context);
  data->embedder_fields_serializers_.push_back(callback);
  return index;
}

size_t SnapshotCreator::AddTemplate(Local<Template> template_obj) {
  return AddData(template_obj);
}

size_t SnapshotCreator::AddData(i::Address object) {
  DCHECK_NE(object, i::kNullAddress);
  SnapshotCreatorData* data = SnapshotCreatorData::cast(data_);
  DCHECK(!data->created_);
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(data->isolate_);
  i::HandleScope scope(isolate);
  i::Handle<i::Object> obj(reinterpret_cast<i::Object*>(object), isolate);
  i::Handle<i::ArrayList> list;
  if (!isolate->heap()->serialized_objects()->IsArrayList()) {
    list = i::ArrayList::New(isolate, 1);
  } else {
    list = i::Handle<i::ArrayList>(
        i::ArrayList::cast(isolate->heap()->serialized_objects()), isolate);
  }
  size_t index = static_cast<size_t>(list->Length());
  list = i::ArrayList::Add(isolate, list, obj);
  isolate->heap()->SetSerializedObjects(*list);
  return index;
}

size_t SnapshotCreator::AddData(Local<Context> context, i::Address object) {
  DCHECK_NE(object, i::kNullAddress);
  DCHECK(!SnapshotCreatorData::cast(data_)->created_);
  i::Handle<i::Context> ctx = Utils::OpenHandle(*context);
  i::Isolate* isolate = ctx->GetIsolate();
  i::HandleScope scope(isolate);
  i::Handle<i::Object> obj(reinterpret_cast<i::Object*>(object), isolate);
  i::Handle<i::ArrayList> list;
  if (!ctx->serialized_objects()->IsArrayList()) {
    list = i::ArrayList::New(isolate, 1);
  } else {
    list = i::Handle<i::ArrayList>(
        i::ArrayList::cast(ctx->serialized_objects()), isolate);
  }
  size_t index = static_cast<size_t>(list->Length());
  list = i::ArrayList::Add(isolate, list, obj);
  ctx->set_serialized_objects(*list);
  return index;
}

namespace {
void ConvertSerializedObjectsToFixedArray(Local<Context> context) {
  i::Handle<i::Context> ctx = Utils::OpenHandle(*context);
  i::Isolate* isolate = ctx->GetIsolate();
  if (!ctx->serialized_objects()->IsArrayList()) {
    ctx->set_serialized_objects(i::ReadOnlyRoots(isolate).empty_fixed_array());
  } else {
    i::Handle<i::ArrayList> list(i::ArrayList::cast(ctx->serialized_objects()),
                                 isolate);
    i::Handle<i::FixedArray> elements = i::ArrayList::Elements(isolate, list);
    ctx->set_serialized_objects(*elements);
  }
}

void ConvertSerializedObjectsToFixedArray(i::Isolate* isolate) {
  if (!isolate->heap()->serialized_objects()->IsArrayList()) {
    isolate->heap()->SetSerializedObjects(
        i::ReadOnlyRoots(isolate).empty_fixed_array());
  } else {
    i::Handle<i::ArrayList> list(
        i::ArrayList::cast(isolate->heap()->serialized_objects()), isolate);
    i::Handle<i::FixedArray> elements = i::ArrayList::Elements(isolate, list);
    isolate->heap()->SetSerializedObjects(*elements);
  }
}
}  // anonymous namespace

StartupData SnapshotCreator::CreateBlob(
    SnapshotCreator::FunctionCodeHandling function_code_handling) {
  SnapshotCreatorData* data = SnapshotCreatorData::cast(data_);
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(data->isolate_);
  DCHECK(!data->created_);
  DCHECK(!data->default_context_.IsEmpty());

  int num_additional_contexts = static_cast<int>(data->contexts_.Size());

  {
    i::HandleScope scope(isolate);
    // Convert list of context-independent data to FixedArray.
    ConvertSerializedObjectsToFixedArray(isolate);

    // Convert lists of context-dependent data to FixedArray.
    ConvertSerializedObjectsToFixedArray(
        data->default_context_.Get(data->isolate_));
    for (int i = 0; i < num_additional_contexts; i++) {
      ConvertSerializedObjectsToFixedArray(data->contexts_.Get(i));
    }

    // We need to store the global proxy size upfront in case we need the
    // bootstrapper to create a global proxy before we deserialize the context.
    i::Handle<i::FixedArray> global_proxy_sizes =
        isolate->factory()->NewFixedArray(num_additional_contexts, i::TENURED);
    for (int i = 0; i < num_additional_contexts; i++) {
      i::Handle<i::Context> context =
          v8::Utils::OpenHandle(*data->contexts_.Get(i));
      global_proxy_sizes->set(i,
                              i::Smi::FromInt(context->global_proxy()->Size()));
    }
    isolate->heap()->SetSerializedGlobalProxySizes(*global_proxy_sizes);
  }

  // We might rehash strings and re-sort descriptors. Clear the lookup cache.
  isolate->descriptor_lookup_cache()->Clear();

  // If we don't do this then we end up with a stray root pointing at the
  // context even after we have disposed of the context.
  isolate->heap()->CollectAllAvailableGarbage(
      i::GarbageCollectionReason::kSnapshotCreator);
  {
    i::HandleScope scope(isolate);
    isolate->heap()->CompactWeakArrayLists(internal::TENURED);
  }

  isolate->heap()->read_only_space()->ClearStringPaddingIfNeeded();

  if (function_code_handling == FunctionCodeHandling::kClear) {
    // Clear out re-compilable data from all shared function infos. Any
    // JSFunctions using these SFIs will have their code pointers reset by the
    // partial serializer.
    //
    // We have to iterate the heap and collect handles to each clearable SFI,
    // before we disable allocation, since we have to allocate UncompiledDatas
    // to be able to recompile them.
    i::HandleScope scope(isolate);
    std::vector<i::Handle<i::SharedFunctionInfo>> sfis_to_clear;

    i::HeapIterator heap_iterator(isolate->heap());
    while (i::HeapObject* current_obj = heap_iterator.next()) {
      if (current_obj->IsSharedFunctionInfo()) {
        i::SharedFunctionInfo* shared =
            i::SharedFunctionInfo::cast(current_obj);
        if (shared->CanDiscardCompiled()) {
          sfis_to_clear.emplace_back(shared, isolate);
        }
      }
    }
    i::AllowHeapAllocation allocate_for_discard;
    for (i::Handle<i::SharedFunctionInfo> shared : sfis_to_clear) {
      i::SharedFunctionInfo::DiscardCompiled(isolate, shared);
    }
  }

  i::DisallowHeapAllocation no_gc_from_here_on;

  int num_contexts = num_additional_contexts + 1;
  std::vector<i::Context*> contexts;
  contexts.reserve(num_contexts);
  {
    i::HandleScope scope(isolate);
    contexts.push_back(
        *v8::Utils::OpenHandle(*data->default_context_.Get(data->isolate_)));
    data->default_context_.Reset();
    for (int i = 0; i < num_additional_contexts; i++) {
      i::Handle<i::Context> context =
          v8::Utils::OpenHandle(*data->contexts_.Get(i));
      contexts.push_back(*context);
    }
    data->contexts_.Clear();
  }

  // Check that values referenced by global/eternal handles are accounted for.
  i::SerializedHandleChecker handle_checker(isolate, &contexts);
  CHECK(handle_checker.CheckGlobalAndEternalHandles());

  i::HeapIterator heap_iterator(isolate->heap());
  while (i::HeapObject* current_obj = heap_iterator.next()) {
    if (current_obj->IsJSFunction()) {
      i::JSFunction* fun = i::JSFunction::cast(current_obj);

      // Complete in-object slack tracking for all functions.
      fun->CompleteInobjectSlackTrackingIfActive();

      // Also, clear out feedback vectors, or any optimized code.
      if (fun->has_feedback_vector()) {
        fun->feedback_cell()->set_value(
            i::ReadOnlyRoots(isolate).undefined_value());
        fun->set_code(isolate->builtins()->builtin(i::Builtins::kCompileLazy));
      }
      if (function_code_handling == FunctionCodeHandling::kClear) {
        DCHECK(fun->shared()->HasWasmExportedFunctionData() ||
               fun->shared()->HasBuiltinId() ||
               fun->shared()->IsApiFunction() ||
               fun->shared()->HasUncompiledDataWithoutPreParsedScope());
      }
    }
  }

  i::ReadOnlySerializer read_only_serializer(isolate);
  read_only_serializer.SerializeReadOnlyRoots();

  i::StartupSerializer startup_serializer(isolate, &read_only_serializer);
  startup_serializer.SerializeStrongReferences();

  // Serialize each context with a new partial serializer.
  std::vector<i::SnapshotData*> context_snapshots;
  context_snapshots.reserve(num_contexts);

  // TODO(6593): generalize rehashing, and remove this flag.
  bool can_be_rehashed = true;

  for (int i = 0; i < num_contexts; i++) {
    bool is_default_context = i == 0;
    i::PartialSerializer partial_serializer(
        isolate, &startup_serializer,
        is_default_context ? data->default_embedder_fields_serializer_
                           : data->embedder_fields_serializers_[i - 1]);
    partial_serializer.Serialize(&contexts[i], !is_default_context);
    can_be_rehashed = can_be_rehashed && partial_serializer.can_be_rehashed();
    context_snapshots.push_back(new i::SnapshotData(&partial_serializer));
  }

  // Builtin serialization places additional objects into the partial snapshot
  // cache and thus needs to happen before SerializeWeakReferencesAndDeferred
  // is called below.
  i::BuiltinSerializer builtin_serializer(isolate, &startup_serializer);
  builtin_serializer.SerializeBuiltinsAndHandlers();

  startup_serializer.SerializeWeakReferencesAndDeferred();
  can_be_rehashed = can_be_rehashed && startup_serializer.can_be_rehashed();

  read_only_serializer.FinalizeSerialization();
  can_be_rehashed = can_be_rehashed && read_only_serializer.can_be_rehashed();

  i::SnapshotData read_only_snapshot(&read_only_serializer);
  i::SnapshotData startup_snapshot(&startup_serializer);
  i::BuiltinSnapshotData builtin_snapshot(&builtin_serializer);
  StartupData result = i::Snapshot::CreateSnapshotBlob(
      &startup_snapshot, &builtin_snapshot, &read_only_snapshot,
      context_snapshots, can_be_rehashed);

  // Delete heap-allocated context snapshot instances.
  for (const auto context_snapshot : context_snapshots) {
    delete context_snapshot;
  }
  data->created_ = true;

  DCHECK(i::Snapshot::VerifyChecksum(&result));
  return result;
}

void V8::SetDcheckErrorHandler(DcheckErrorCallback that) {
  v8::base::SetDcheckFunction(that);
}

void V8::SetFlagsFromString(const char* str, int length) {
  i::FlagList::SetFlagsFromString(str, length);
  i::FlagList::EnforceFlagImplications();
}


void V8::SetFlagsFromCommandLine(int* argc, char** argv, bool remove_flags) {
  i::FlagList::SetFlagsFromCommandLine(argc, argv, remove_flags);
}

RegisteredExtension* RegisteredExtension::first_extension_ = nullptr;

RegisteredExtension::RegisteredExtension(Extension* extension)
    : extension_(extension) { }


void RegisteredExtension::Register(RegisteredExtension* that) {
  that->next_ = first_extension_;
  first_extension_ = that;
}


void RegisteredExtension::UnregisterAll() {
  RegisteredExtension* re = first_extension_;
  while (re != nullptr) {
    RegisteredExtension* next = re->next();
    delete re;
    re = next;
  }
  first_extension_ = nullptr;
}

namespace {
class ExtensionResource : public String::ExternalOneByteStringResource {
 public:
  ExtensionResource() : data_(nullptr), length_(0) {}
  ExtensionResource(const char* data, size_t length)
      : data_(data), length_(length) {}
  const char* data() const override { return data_; }
  size_t length() const override { return length_; }
  void Dispose() override {}

 private:
  const char* data_;
  size_t length_;
};
}  // anonymous namespace

void RegisterExtension(Extension* that) {
  RegisteredExtension* extension = new RegisteredExtension(that);
  RegisteredExtension::Register(extension);
}


Extension::Extension(const char* name,
                     const char* source,
                     int dep_count,
                     const char** deps,
                     int source_length)
    : name_(name),
      source_length_(source_length >= 0 ?
                     source_length :
                     (source ? static_cast<int>(strlen(source)) : 0)),
      dep_count_(dep_count),
      deps_(deps),
      auto_enable_(false) {
  source_ = new ExtensionResource(source, source_length_);
  CHECK(source != nullptr || source_length_ == 0);
}

ResourceConstraints::ResourceConstraints()
    : max_semi_space_size_in_kb_(0),
      max_old_space_size_(0),
      stack_limit_(nullptr),
      code_range_size_(0),
      max_zone_pool_size_(0) {}

void ResourceConstraints::ConfigureDefaults(uint64_t physical_memory,
                                            uint64_t virtual_memory_limit) {
  set_max_semi_space_size_in_kb(
      i::Heap::ComputeMaxSemiSpaceSize(physical_memory));
  set_max_old_space_size(i::Heap::ComputeMaxOldGenerationSize(physical_memory));
  set_max_zone_pool_size(i::AccountingAllocator::kMaxPoolSize);

  if (virtual_memory_limit > 0 && i::kRequiresCodeRange) {
    // Reserve no more than 1/8 of the memory for the code range, but at most
    // kMaximalCodeRangeSize.
    set_code_range_size(
        i::Min(i::kMaximalCodeRangeSize / i::MB,
               static_cast<size_t>((virtual_memory_limit >> 3) / i::MB)));
  }
}

void SetResourceConstraints(i::Isolate* isolate,
                            const ResourceConstraints& constraints) {
  size_t semi_space_size = constraints.max_semi_space_size_in_kb();
  size_t old_space_size = constraints.max_old_space_size();
  size_t code_range_size = constraints.code_range_size();
  size_t max_pool_size = constraints.max_zone_pool_size();
  if (semi_space_size != 0 || old_space_size != 0 || code_range_size != 0) {
    isolate->heap()->ConfigureHeap(semi_space_size, old_space_size,
                                   code_range_size);
  }
  isolate->allocator()->ConfigureSegmentPool(max_pool_size);

  if (constraints.stack_limit() != nullptr) {
    uintptr_t limit = reinterpret_cast<uintptr_t>(constraints.stack_limit());
    isolate->stack_guard()->SetStackLimit(limit);
  }
}

i::Address* V8::GlobalizeReference(i::Isolate* isolate, i::Address* obj) {
  LOG_API(isolate, Persistent, New);
  i::Handle<i::Object> result = isolate->global_handles()->Create(*obj);
#ifdef VERIFY_HEAP
  if (i::FLAG_verify_heap) {
    reinterpret_cast<i::Object*>(*obj)->ObjectVerify(isolate);
  }
#endif  // VERIFY_HEAP
  return result.location_as_address_ptr();
}

i::Address* V8::CopyPersistent(i::Address* obj) {
  i::Handle<i::Object> result = i::GlobalHandles::CopyGlobal(obj);
  return result.location_as_address_ptr();
}

void V8::RegisterExternallyReferencedObject(i::Address* location,
                                            i::Isolate* isolate) {
  isolate->heap()->RegisterExternallyReferencedObject(location);
}

void V8::MakeWeak(i::Address* location, void* parameter,
                  WeakCallbackInfo<void>::Callback weak_callback,
                  WeakCallbackType type) {
  i::GlobalHandles::MakeWeak(location, parameter, weak_callback, type);
}

void V8::MakeWeak(i::Address** location_addr) {
  i::GlobalHandles::MakeWeak(location_addr);
}

void* V8::ClearWeak(i::Address* location) {
  return i::GlobalHandles::ClearWeakness(location);
}

void V8::AnnotateStrongRetainer(i::Address* location, const char* label) {
  i::GlobalHandles::AnnotateStrongRetainer(location, label);
}

void V8::DisposeGlobal(i::Address* location) {
  i::GlobalHandles::Destroy(location);
}

Value* V8::Eternalize(Isolate* v8_isolate, Value* value) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  i::Object* object = *Utils::OpenHandle(value);
  int index = -1;
  isolate->eternal_handles()->Create(isolate, object, &index);
  return reinterpret_cast<Value*>(
      isolate->eternal_handles()->Get(index).location());
}


void V8::FromJustIsNothing() {
  Utils::ApiCheck(false, "v8::FromJust", "Maybe value is Nothing.");
}


void V8::ToLocalEmpty() {
  Utils::ApiCheck(false, "v8::ToLocalChecked", "Empty MaybeLocal.");
}

void V8::InternalFieldOutOfBounds(int index) {
  Utils::ApiCheck(0 <= index && index < kInternalFieldsInWeakCallback,
                  "WeakCallbackInfo::GetInternalField",
                  "Internal field out of bounds.");
}


// --- H a n d l e s ---


HandleScope::HandleScope(Isolate* isolate) {
  Initialize(isolate);
}


void HandleScope::Initialize(Isolate* isolate) {
  i::Isolate* internal_isolate = reinterpret_cast<i::Isolate*>(isolate);
  // We do not want to check the correct usage of the Locker class all over the
  // place, so we do it only here: Without a HandleScope, an embedder can do
  // almost nothing, so it is enough to check in this central place.
  // We make an exception if the serializer is enabled, which means that the
  // Isolate is exclusively used to create a snapshot.
  Utils::ApiCheck(
      !v8::Locker::IsActive() ||
          internal_isolate->thread_manager()->IsLockedByCurrentThread() ||
          internal_isolate->serializer_enabled(),
      "HandleScope::HandleScope",
      "Entering the V8 API without proper locking in place");
  i::HandleScopeData* current = internal_isolate->handle_scope_data();
  isolate_ = internal_isolate;
  prev_next_ = reinterpret_cast<i::Address*>(current->next);
  prev_limit_ = reinterpret_cast<i::Address*>(current->limit);
  current->level++;
}


HandleScope::~HandleScope() {
  i::HandleScope::CloseScope(isolate_,
                             reinterpret_cast<i::Object**>(prev_next_),
                             reinterpret_cast<i::Object**>(prev_limit_));
}

void* HandleScope::operator new(size_t) { base::OS::Abort(); }
void* HandleScope::operator new[](size_t) { base::OS::Abort(); }
void HandleScope::operator delete(void*, size_t) { base::OS::Abort(); }
void HandleScope::operator delete[](void*, size_t) { base::OS::Abort(); }

int HandleScope::NumberOfHandles(Isolate* isolate) {
  return i::HandleScope::NumberOfHandles(
      reinterpret_cast<i::Isolate*>(isolate));
}

i::Address* HandleScope::CreateHandle(i::Isolate* isolate, i::Address value) {
  return i::HandleScope::CreateHandle(isolate, value);
}

i::Address* HandleScope::CreateHandle(
    i::NeverReadOnlySpaceObject* writable_object, i::Address value) {
  DCHECK(reinterpret_cast<i::HeapObject*>(writable_object)->IsHeapObject());
  return i::HandleScope::CreateHandle(writable_object->GetIsolate(), value);
}


EscapableHandleScope::EscapableHandleScope(Isolate* v8_isolate) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  escape_slot_ = CreateHandle(
      isolate,
      reinterpret_cast<i::Address>(i::ReadOnlyRoots(isolate).the_hole_value()));
  Initialize(v8_isolate);
}

i::Address* EscapableHandleScope::Escape(i::Address* escape_value) {
  i::Heap* heap = reinterpret_cast<i::Isolate*>(GetIsolate())->heap();
  Utils::ApiCheck(
      reinterpret_cast<i::Object*>(*escape_slot_)->IsTheHole(heap->isolate()),
      "EscapableHandleScope::Escape", "Escape value set twice");
  if (escape_value == nullptr) {
    *escape_slot_ =
        reinterpret_cast<i::Address>(i::ReadOnlyRoots(heap).undefined_value());
    return nullptr;
  }
  *escape_slot_ = *escape_value;
  return escape_slot_;
}

void* EscapableHandleScope::operator new(size_t) { base::OS::Abort(); }
void* EscapableHandleScope::operator new[](size_t) { base::OS::Abort(); }
void EscapableHandleScope::operator delete(void*, size_t) { base::OS::Abort(); }
void EscapableHandleScope::operator delete[](void*, size_t) {
  base::OS::Abort();
}

SealHandleScope::SealHandleScope(Isolate* isolate)
    : isolate_(reinterpret_cast<i::Isolate*>(isolate)) {
  i::HandleScopeData* current = isolate_->handle_scope_data();
  prev_limit_ = reinterpret_cast<i::Address*>(current->limit);
  current->limit = current->next;
  prev_sealed_level_ = current->sealed_level;
  current->sealed_level = current->level;
}


SealHandleScope::~SealHandleScope() {
  i::HandleScopeData* current = isolate_->handle_scope_data();
  DCHECK_EQ(current->next, current->limit);
  current->limit = reinterpret_cast<i::Object**>(prev_limit_);
  DCHECK_EQ(current->level, current->sealed_level);
  current->sealed_level = prev_sealed_level_;
}

void* SealHandleScope::operator new(size_t) { base::OS::Abort(); }
void* SealHandleScope::operator new[](size_t) { base::OS::Abort(); }
void SealHandleScope::operator delete(void*, size_t) { base::OS::Abort(); }
void SealHandleScope::operator delete[](void*, size_t) { base::OS::Abort(); }

void Context::Enter() {
  i::Handle<i::Context> env = Utils::OpenHandle(this);
  i::Isolate* isolate = env->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScopeImplementer* impl = isolate->handle_scope_implementer();
  impl->EnterContext(env);
  impl->SaveContext(isolate->context());
  isolate->set_context(*env);
}

void Context::Exit() {
  i::Handle<i::Context> env = Utils::OpenHandle(this);
  i::Isolate* isolate = env->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScopeImplementer* impl = isolate->handle_scope_implementer();
  if (!Utils::ApiCheck(impl->LastEnteredContextWas(env),
                       "v8::Context::Exit()",
                       "Cannot exit non-entered context")) {
    return;
  }
  impl->LeaveContext();
  isolate->set_context(impl->RestoreContext());
}

Context::BackupIncumbentScope::BackupIncumbentScope(
    Local<Context> backup_incumbent_context)
    : backup_incumbent_context_(backup_incumbent_context) {
  DCHECK(!backup_incumbent_context_.IsEmpty());

  i::Handle<i::Context> env = Utils::OpenHandle(*backup_incumbent_context_);
  i::Isolate* isolate = env->GetIsolate();
  prev_ = isolate->top_backup_incumbent_scope();
  isolate->set_top_backup_incumbent_scope(this);
}

Context::BackupIncumbentScope::~BackupIncumbentScope() {
  i::Handle<i::Context> env = Utils::OpenHandle(*backup_incumbent_context_);
  i::Isolate* isolate = env->GetIsolate();
  isolate->set_top_backup_incumbent_scope(prev_);
}

static void* DecodeSmiToAligned(i::Object* value, const char* location) {
  Utils::ApiCheck(value->IsSmi(), location, "Not a Smi");
  return reinterpret_cast<void*>(value);
}


static i::Smi* EncodeAlignedAsSmi(void* value, const char* location) {
  i::Smi* smi = reinterpret_cast<i::Smi*>(value);
  Utils::ApiCheck(smi->IsSmi(), location, "Pointer is not aligned");
  return smi;
}


static i::Handle<i::FixedArray> EmbedderDataFor(Context* context,
                                                int index,
                                                bool can_grow,
                                                const char* location) {
  i::Handle<i::Context> env = Utils::OpenHandle(context);
  i::Isolate* isolate = env->GetIsolate();
  bool ok =
      Utils::ApiCheck(env->IsNativeContext(),
                      location,
                      "Not a native context") &&
      Utils::ApiCheck(index >= 0, location, "Negative index");
  if (!ok) return i::Handle<i::FixedArray>();
  i::Handle<i::FixedArray> data(env->embedder_data(), isolate);
  if (index < data->length()) return data;
  if (!Utils::ApiCheck(can_grow, location, "Index too large")) {
    return i::Handle<i::FixedArray>();
  }
  int new_size = index + 1;
  int grow_by = new_size - data->length();
  data = isolate->factory()->CopyFixedArrayAndGrow(data, grow_by);
  env->set_embedder_data(*data);
  return data;
}

uint32_t Context::GetNumberOfEmbedderDataFields() {
  i::Handle<i::Context> context = Utils::OpenHandle(this);
  CHECK(context->IsNativeContext());
  return static_cast<uint32_t>(context->embedder_data()->length());
}

v8::Local<v8::Value> Context::SlowGetEmbedderData(int index) {
  const char* location = "v8::Context::GetEmbedderData()";
  i::Handle<i::FixedArray> data = EmbedderDataFor(this, index, false, location);
  if (data.is_null()) return Local<Value>();
  i::Handle<i::Object> result(
      data->get(index),
      reinterpret_cast<i::Isolate*>(Utils::OpenHandle(this)->GetIsolate()));
  return Utils::ToLocal(result);
}


void Context::SetEmbedderData(int index, v8::Local<Value> value) {
  const char* location = "v8::Context::SetEmbedderData()";
  i::Handle<i::FixedArray> data = EmbedderDataFor(this, index, true, location);
  if (data.is_null()) return;
  i::Handle<i::Object> val = Utils::OpenHandle(*value);
  data->set(index, *val);
  DCHECK_EQ(*Utils::OpenHandle(*value),
            *Utils::OpenHandle(*GetEmbedderData(index)));
}


void* Context::SlowGetAlignedPointerFromEmbedderData(int index) {
  const char* location = "v8::Context::GetAlignedPointerFromEmbedderData()";
  i::Handle<i::FixedArray> data = EmbedderDataFor(this, index, false, location);
  if (data.is_null()) return nullptr;
  return DecodeSmiToAligned(data->get(index), location);
}


void Context::SetAlignedPointerInEmbedderData(int index, void* value) {
  const char* location = "v8::Context::SetAlignedPointerInEmbedderData()";
  i::Handle<i::FixedArray> data = EmbedderDataFor(this, index, true, location);
  data->set(index, EncodeAlignedAsSmi(value, location));
  DCHECK_EQ(value, GetAlignedPointerFromEmbedderData(index));
}


// --- T e m p l a t e ---


static void InitializeTemplate(i::Handle<i::TemplateInfo> that, int type) {
  that->set_number_of_properties(0);
  that->set_tag(i::Smi::FromInt(type));
}


void Template::Set(v8::Local<Name> name, v8::Local<Data> value,
                   v8::PropertyAttribute attribute) {
  auto templ = Utils::OpenHandle(this);
  i::Isolate* isolate = templ->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto value_obj = Utils::OpenHandle(*value);
  CHECK(!value_obj->IsJSReceiver() || value_obj->IsTemplateInfo());
  if (value_obj->IsObjectTemplateInfo()) {
    templ->set_serial_number(i::Smi::kZero);
    if (templ->IsFunctionTemplateInfo()) {
      i::Handle<i::FunctionTemplateInfo>::cast(templ)->set_do_not_cache(true);
    }
  }
  i::ApiNatives::AddDataProperty(isolate, templ, Utils::OpenHandle(*name),
                                 value_obj,
                                 static_cast<i::PropertyAttributes>(attribute));
}

void Template::SetPrivate(v8::Local<Private> name, v8::Local<Data> value,
                          v8::PropertyAttribute attribute) {
  Set(Utils::ToLocal(Utils::OpenHandle(reinterpret_cast<Name*>(*name))), value,
      attribute);
}

void Template::SetAccessorProperty(
    v8::Local<v8::Name> name,
    v8::Local<FunctionTemplate> getter,
    v8::Local<FunctionTemplate> setter,
    v8::PropertyAttribute attribute,
    v8::AccessControl access_control) {
  // TODO(verwaest): Remove |access_control|.
  DCHECK_EQ(v8::DEFAULT, access_control);
  auto templ = Utils::OpenHandle(this);
  auto isolate = templ->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  DCHECK(!name.IsEmpty());
  DCHECK(!getter.IsEmpty() || !setter.IsEmpty());
  i::HandleScope scope(isolate);
  i::ApiNatives::AddAccessorProperty(
      isolate, templ, Utils::OpenHandle(*name),
      Utils::OpenHandle(*getter, true), Utils::OpenHandle(*setter, true),
      static_cast<i::PropertyAttributes>(attribute));
}


// --- F u n c t i o n   T e m p l a t e ---
static void InitializeFunctionTemplate(
    i::Handle<i::FunctionTemplateInfo> info) {
  InitializeTemplate(info, Consts::FUNCTION_TEMPLATE);
  info->set_flag(0);
}

static Local<ObjectTemplate> ObjectTemplateNew(
    i::Isolate* isolate, v8::Local<FunctionTemplate> constructor,
    bool do_not_cache);

Local<ObjectTemplate> FunctionTemplate::PrototypeTemplate() {
  i::Isolate* i_isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  i::Handle<i::Object> result(Utils::OpenHandle(this)->prototype_template(),
                              i_isolate);
  if (result->IsUndefined(i_isolate)) {
    // Do not cache prototype objects.
    result = Utils::OpenHandle(
        *ObjectTemplateNew(i_isolate, Local<FunctionTemplate>(), true));
    Utils::OpenHandle(this)->set_prototype_template(*result);
  }
  return ToApiHandle<ObjectTemplate>(result);
}

void FunctionTemplate::SetPrototypeProviderTemplate(
    Local<FunctionTemplate> prototype_provider) {
  i::Isolate* i_isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  i::Handle<i::Object> result = Utils::OpenHandle(*prototype_provider);
  auto info = Utils::OpenHandle(this);
  CHECK(info->prototype_template()->IsUndefined(i_isolate));
  CHECK(info->parent_template()->IsUndefined(i_isolate));
  info->set_prototype_provider_template(*result);
}

static void EnsureNotInstantiated(i::Handle<i::FunctionTemplateInfo> info,
                                  const char* func) {
  Utils::ApiCheck(!info->instantiated(), func,
                  "FunctionTemplate already instantiated");
}


void FunctionTemplate::Inherit(v8::Local<FunctionTemplate> value) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::Inherit");
  i::Isolate* i_isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  CHECK(info->prototype_provider_template()->IsUndefined(i_isolate));
  info->set_parent_template(*Utils::OpenHandle(*value));
}

static Local<FunctionTemplate> FunctionTemplateNew(
    i::Isolate* isolate, FunctionCallback callback, v8::Local<Value> data,
    v8::Local<Signature> signature, int length, bool do_not_cache,
    v8::Local<Private> cached_property_name = v8::Local<Private>(),
    SideEffectType side_effect_type = SideEffectType::kHasSideEffect) {
  i::Handle<i::Struct> struct_obj =
      isolate->factory()->NewStruct(i::FUNCTION_TEMPLATE_INFO_TYPE, i::TENURED);
  i::Handle<i::FunctionTemplateInfo> obj =
      i::Handle<i::FunctionTemplateInfo>::cast(struct_obj);
  InitializeFunctionTemplate(obj);
  obj->set_do_not_cache(do_not_cache);
  int next_serial_number = i::FunctionTemplateInfo::kInvalidSerialNumber;
  if (!do_not_cache) {
    next_serial_number = isolate->heap()->GetNextTemplateSerialNumber();
  }
  obj->set_serial_number(i::Smi::FromInt(next_serial_number));
  if (callback != nullptr) {
    Utils::ToLocal(obj)->SetCallHandler(callback, data, side_effect_type);
  }
  obj->set_length(length);
  obj->set_undetectable(false);
  obj->set_needs_access_check(false);
  obj->set_accept_any_receiver(true);
  if (!signature.IsEmpty()) {
    obj->set_signature(*Utils::OpenHandle(*signature));
  }
  obj->set_cached_property_name(
      cached_property_name.IsEmpty()
          ? i::ReadOnlyRoots(isolate).the_hole_value()
          : *Utils::OpenHandle(*cached_property_name));
  return Utils::ToLocal(obj);
}

Local<FunctionTemplate> FunctionTemplate::New(
    Isolate* isolate, FunctionCallback callback, v8::Local<Value> data,
    v8::Local<Signature> signature, int length, ConstructorBehavior behavior,
    SideEffectType side_effect_type) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  // Changes to the environment cannot be captured in the snapshot. Expect no
  // function templates when the isolate is created for serialization.
  LOG_API(i_isolate, FunctionTemplate, New);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  auto templ = FunctionTemplateNew(i_isolate, callback, data, signature, length,
                                   false, Local<Private>(), side_effect_type);
  if (behavior == ConstructorBehavior::kThrow) templ->RemovePrototype();
  return templ;
}

MaybeLocal<FunctionTemplate> FunctionTemplate::FromSnapshot(Isolate* isolate,
                                                            size_t index) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  i::FixedArray* serialized_objects = i_isolate->heap()->serialized_objects();
  int int_index = static_cast<int>(index);
  if (int_index < serialized_objects->length()) {
    i::Object* info = serialized_objects->get(int_index);
    if (info->IsFunctionTemplateInfo()) {
      return Utils::ToLocal(i::Handle<i::FunctionTemplateInfo>(
          i::FunctionTemplateInfo::cast(info), i_isolate));
    }
  }
  return Local<FunctionTemplate>();
}

Local<FunctionTemplate> FunctionTemplate::NewWithCache(
    Isolate* isolate, FunctionCallback callback, Local<Private> cache_property,
    Local<Value> data, Local<Signature> signature, int length,
    SideEffectType side_effect_type) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  LOG_API(i_isolate, FunctionTemplate, NewWithCache);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  return FunctionTemplateNew(i_isolate, callback, data, signature, length,
                             false, cache_property, side_effect_type);
}

Local<Signature> Signature::New(Isolate* isolate,
                                Local<FunctionTemplate> receiver) {
  return Utils::SignatureToLocal(Utils::OpenHandle(*receiver));
}


Local<AccessorSignature> AccessorSignature::New(
    Isolate* isolate, Local<FunctionTemplate> receiver) {
  return Utils::AccessorSignatureToLocal(Utils::OpenHandle(*receiver));
}

#define SET_FIELD_WRAPPED(isolate, obj, setter, cdata)        \
  do {                                                        \
    i::Handle<i::Object> foreign = FromCData(isolate, cdata); \
    (obj)->setter(*foreign);                                  \
  } while (false)

void FunctionTemplate::SetCallHandler(FunctionCallback callback,
                                      v8::Local<Value> data,
                                      SideEffectType side_effect_type) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::SetCallHandler");
  i::Isolate* isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  i::Handle<i::CallHandlerInfo> obj = isolate->factory()->NewCallHandlerInfo(
      side_effect_type == SideEffectType::kHasNoSideEffect);
  SET_FIELD_WRAPPED(isolate, obj, set_callback, callback);
  SET_FIELD_WRAPPED(isolate, obj, set_js_callback, obj->redirected_callback());
  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  obj->set_data(*Utils::OpenHandle(*data));
  info->set_call_code(*obj);
}


namespace {

template <typename Getter, typename Setter>
i::Handle<i::AccessorInfo> MakeAccessorInfo(
    i::Isolate* isolate, v8::Local<Name> name, Getter getter, Setter setter,
    v8::Local<Value> data, v8::AccessControl settings,
    v8::Local<AccessorSignature> signature, bool is_special_data_property,
    bool replace_on_access) {
  i::Handle<i::AccessorInfo> obj = isolate->factory()->NewAccessorInfo();
  SET_FIELD_WRAPPED(isolate, obj, set_getter, getter);
  DCHECK_IMPLIES(replace_on_access,
                 is_special_data_property && setter == nullptr);
  if (is_special_data_property && setter == nullptr) {
    setter = reinterpret_cast<Setter>(&i::Accessors::ReconfigureToDataProperty);
  }
  SET_FIELD_WRAPPED(isolate, obj, set_setter, setter);
  i::Address redirected = obj->redirected_getter();
  if (redirected != i::kNullAddress) {
    SET_FIELD_WRAPPED(isolate, obj, set_js_getter, redirected);
  }
  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  obj->set_data(*Utils::OpenHandle(*data));
  obj->set_is_special_data_property(is_special_data_property);
  obj->set_replace_on_access(replace_on_access);
  i::Handle<i::Name> accessor_name = Utils::OpenHandle(*name);
  if (!accessor_name->IsUniqueName()) {
    accessor_name = isolate->factory()->InternalizeString(
        i::Handle<i::String>::cast(accessor_name));
  }
  obj->set_name(*accessor_name);
  if (settings & ALL_CAN_READ) obj->set_all_can_read(true);
  if (settings & ALL_CAN_WRITE) obj->set_all_can_write(true);
  obj->set_initial_property_attributes(i::NONE);
  if (!signature.IsEmpty()) {
    obj->set_expected_receiver_type(*Utils::OpenHandle(*signature));
  }
  return obj;
}

}  // namespace

Local<ObjectTemplate> FunctionTemplate::InstanceTemplate() {
  i::Handle<i::FunctionTemplateInfo> handle = Utils::OpenHandle(this, true);
  if (!Utils::ApiCheck(!handle.is_null(),
                       "v8::FunctionTemplate::InstanceTemplate()",
                       "Reading from empty handle")) {
    return Local<ObjectTemplate>();
  }
  i::Isolate* isolate = handle->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  if (handle->instance_template()->IsUndefined(isolate)) {
    Local<ObjectTemplate> templ =
        ObjectTemplate::New(isolate, ToApiHandle<FunctionTemplate>(handle));
    handle->set_instance_template(*Utils::OpenHandle(*templ));
  }
  i::Handle<i::ObjectTemplateInfo> result(
      i::ObjectTemplateInfo::cast(handle->instance_template()), isolate);
  return Utils::ToLocal(result);
}


void FunctionTemplate::SetLength(int length) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::SetLength");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_length(length);
}


void FunctionTemplate::SetClassName(Local<String> name) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::SetClassName");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_class_name(*Utils::OpenHandle(*name));
}


void FunctionTemplate::SetAcceptAnyReceiver(bool value) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::SetAcceptAnyReceiver");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_accept_any_receiver(value);
}


void FunctionTemplate::SetHiddenPrototype(bool value) {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::SetHiddenPrototype");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_hidden_prototype(value);
}


void FunctionTemplate::ReadOnlyPrototype() {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::ReadOnlyPrototype");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_read_only_prototype(true);
}


void FunctionTemplate::RemovePrototype() {
  auto info = Utils::OpenHandle(this);
  EnsureNotInstantiated(info, "v8::FunctionTemplate::RemovePrototype");
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  info->set_remove_prototype(true);
}


// --- O b j e c t T e m p l a t e ---


Local<ObjectTemplate> ObjectTemplate::New(
    Isolate* isolate, v8::Local<FunctionTemplate> constructor) {
  return New(reinterpret_cast<i::Isolate*>(isolate), constructor);
}


static Local<ObjectTemplate> ObjectTemplateNew(
    i::Isolate* isolate, v8::Local<FunctionTemplate> constructor,
    bool do_not_cache) {
  LOG_API(isolate, ObjectTemplate, New);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::Handle<i::Struct> struct_obj =
      isolate->factory()->NewStruct(i::OBJECT_TEMPLATE_INFO_TYPE, i::TENURED);
  i::Handle<i::ObjectTemplateInfo> obj =
      i::Handle<i::ObjectTemplateInfo>::cast(struct_obj);
  InitializeTemplate(obj, Consts::OBJECT_TEMPLATE);
  int next_serial_number = 0;
  if (!do_not_cache) {
    next_serial_number = isolate->heap()->GetNextTemplateSerialNumber();
  }
  obj->set_serial_number(i::Smi::FromInt(next_serial_number));
  if (!constructor.IsEmpty())
    obj->set_constructor(*Utils::OpenHandle(*constructor));
  obj->set_data(i::Smi::kZero);
  return Utils::ToLocal(obj);
}

Local<ObjectTemplate> ObjectTemplate::New(
    i::Isolate* isolate, v8::Local<FunctionTemplate> constructor) {
  return ObjectTemplateNew(isolate, constructor, false);
}

MaybeLocal<ObjectTemplate> ObjectTemplate::FromSnapshot(Isolate* isolate,
                                                        size_t index) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  i::FixedArray* serialized_objects = i_isolate->heap()->serialized_objects();
  int int_index = static_cast<int>(index);
  if (int_index < serialized_objects->length()) {
    i::Object* info = serialized_objects->get(int_index);
    if (info->IsObjectTemplateInfo()) {
      return Utils::ToLocal(i::Handle<i::ObjectTemplateInfo>(
          i::ObjectTemplateInfo::cast(info), i_isolate));
    }
  }
  return Local<ObjectTemplate>();
}

// Ensure that the object template has a constructor.  If no
// constructor is available we create one.
static i::Handle<i::FunctionTemplateInfo> EnsureConstructor(
    i::Isolate* isolate,
    ObjectTemplate* object_template) {
  i::Object* obj = Utils::OpenHandle(object_template)->constructor();
  if (!obj->IsUndefined(isolate)) {
    i::FunctionTemplateInfo* info = i::FunctionTemplateInfo::cast(obj);
    return i::Handle<i::FunctionTemplateInfo>(info, isolate);
  }
  Local<FunctionTemplate> templ =
      FunctionTemplate::New(reinterpret_cast<Isolate*>(isolate));
  i::Handle<i::FunctionTemplateInfo> constructor = Utils::OpenHandle(*templ);
  constructor->set_instance_template(*Utils::OpenHandle(object_template));
  Utils::OpenHandle(object_template)->set_constructor(*constructor);
  return constructor;
}

template <typename Getter, typename Setter, typename Data, typename Template>
static void TemplateSetAccessor(
    Template* template_obj, v8::Local<Name> name, Getter getter, Setter setter,
    Data data, AccessControl settings, PropertyAttribute attribute,
    v8::Local<AccessorSignature> signature, bool is_special_data_property,
    bool replace_on_access, SideEffectType getter_side_effect_type,
    SideEffectType setter_side_effect_type) {
  auto info = Utils::OpenHandle(template_obj);
  auto isolate = info->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  i::Handle<i::AccessorInfo> accessor_info =
      MakeAccessorInfo(isolate, name, getter, setter, data, settings, signature,
                       is_special_data_property, replace_on_access);
  accessor_info->set_initial_property_attributes(
      static_cast<i::PropertyAttributes>(attribute));
  accessor_info->set_getter_side_effect_type(getter_side_effect_type);
  accessor_info->set_setter_side_effect_type(setter_side_effect_type);
  i::ApiNatives::AddNativeDataProperty(isolate, info, accessor_info);
}

void Template::SetNativeDataProperty(
    v8::Local<String> name, AccessorGetterCallback getter,
    AccessorSetterCallback setter, v8::Local<Value> data,
    PropertyAttribute attribute, v8::Local<AccessorSignature> signature,
    AccessControl settings, SideEffectType getter_side_effect_type,
    SideEffectType setter_side_effect_type) {
  TemplateSetAccessor(this, name, getter, setter, data, settings, attribute,
                      signature, true, false, getter_side_effect_type,
                      setter_side_effect_type);
}

void Template::SetNativeDataProperty(
    v8::Local<Name> name, AccessorNameGetterCallback getter,
    AccessorNameSetterCallback setter, v8::Local<Value> data,
    PropertyAttribute attribute, v8::Local<AccessorSignature> signature,
    AccessControl settings, SideEffectType getter_side_effect_type,
    SideEffectType setter_side_effect_type) {
  TemplateSetAccessor(this, name, getter, setter, data, settings, attribute,
                      signature, true, false, getter_side_effect_type,
                      setter_side_effect_type);
}

void Template::SetLazyDataProperty(v8::Local<Name> name,
                                   AccessorNameGetterCallback getter,
                                   v8::Local<Value> data,
                                   PropertyAttribute attribute,
                                   SideEffectType getter_side_effect_type,
                                   SideEffectType setter_side_effect_type) {
  TemplateSetAccessor(this, name, getter,
                      static_cast<AccessorNameSetterCallback>(nullptr), data,
                      DEFAULT, attribute, Local<AccessorSignature>(), true,
                      true, getter_side_effect_type, setter_side_effect_type);
}

void Template::SetIntrinsicDataProperty(Local<Name> name, Intrinsic intrinsic,
                                        PropertyAttribute attribute) {
  auto templ = Utils::OpenHandle(this);
  i::Isolate* isolate = templ->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  i::ApiNatives::AddDataProperty(isolate, templ, Utils::OpenHandle(*name),
                                 intrinsic,
                                 static_cast<i::PropertyAttributes>(attribute));
}

void ObjectTemplate::SetAccessor(v8::Local<String> name,
                                 AccessorGetterCallback getter,
                                 AccessorSetterCallback setter,
                                 v8::Local<Value> data, AccessControl settings,
                                 PropertyAttribute attribute,
                                 v8::Local<AccessorSignature> signature,
                                 SideEffectType getter_side_effect_type,
                                 SideEffectType setter_side_effect_type) {
  TemplateSetAccessor(this, name, getter, setter, data, settings, attribute,
                      signature, i::FLAG_disable_old_api_accessors, false,
                      getter_side_effect_type, setter_side_effect_type);
}

void ObjectTemplate::SetAccessor(v8::Local<Name> name,
                                 AccessorNameGetterCallback getter,
                                 AccessorNameSetterCallback setter,
                                 v8::Local<Value> data, AccessControl settings,
                                 PropertyAttribute attribute,
                                 v8::Local<AccessorSignature> signature,
                                 SideEffectType getter_side_effect_type,
                                 SideEffectType setter_side_effect_type) {
  TemplateSetAccessor(this, name, getter, setter, data, settings, attribute,
                      signature, i::FLAG_disable_old_api_accessors, false,
                      getter_side_effect_type, setter_side_effect_type);
}

template <typename Getter, typename Setter, typename Query, typename Descriptor,
          typename Deleter, typename Enumerator, typename Definer>
static i::Handle<i::InterceptorInfo> CreateInterceptorInfo(
    i::Isolate* isolate, Getter getter, Setter setter, Query query,
    Descriptor descriptor, Deleter remover, Enumerator enumerator,
    Definer definer, Local<Value> data, PropertyHandlerFlags flags) {
  auto obj = i::Handle<i::InterceptorInfo>::cast(
      isolate->factory()->NewStruct(i::INTERCEPTOR_INFO_TYPE, i::TENURED));
  obj->set_flags(0);

  if (getter != nullptr) SET_FIELD_WRAPPED(isolate, obj, set_getter, getter);
  if (setter != nullptr) SET_FIELD_WRAPPED(isolate, obj, set_setter, setter);
  if (query != nullptr) SET_FIELD_WRAPPED(isolate, obj, set_query, query);
  if (descriptor != nullptr)
    SET_FIELD_WRAPPED(isolate, obj, set_descriptor, descriptor);
  if (remover != nullptr) SET_FIELD_WRAPPED(isolate, obj, set_deleter, remover);
  if (enumerator != nullptr)
    SET_FIELD_WRAPPED(isolate, obj, set_enumerator, enumerator);
  if (definer != nullptr) SET_FIELD_WRAPPED(isolate, obj, set_definer, definer);
  obj->set_can_intercept_symbols(
      !(static_cast<int>(flags) &
        static_cast<int>(PropertyHandlerFlags::kOnlyInterceptStrings)));
  obj->set_all_can_read(static_cast<int>(flags) &
                        static_cast<int>(PropertyHandlerFlags::kAllCanRead));
  obj->set_non_masking(static_cast<int>(flags) &
                       static_cast<int>(PropertyHandlerFlags::kNonMasking));
  obj->set_has_no_side_effect(
      static_cast<int>(flags) &
      static_cast<int>(PropertyHandlerFlags::kHasNoSideEffect));

  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  obj->set_data(*Utils::OpenHandle(*data));
  return obj;
}

template <typename Getter, typename Setter, typename Query, typename Descriptor,
          typename Deleter, typename Enumerator, typename Definer>
static i::Handle<i::InterceptorInfo> CreateNamedInterceptorInfo(
    i::Isolate* isolate, Getter getter, Setter setter, Query query,
    Descriptor descriptor, Deleter remover, Enumerator enumerator,
    Definer definer, Local<Value> data, PropertyHandlerFlags flags) {
  auto interceptor =
      CreateInterceptorInfo(isolate, getter, setter, query, descriptor, remover,
                            enumerator, definer, data, flags);
  interceptor->set_is_named(true);
  return interceptor;
}

template <typename Getter, typename Setter, typename Query, typename Descriptor,
          typename Deleter, typename Enumerator, typename Definer>
static i::Handle<i::InterceptorInfo> CreateIndexedInterceptorInfo(
    i::Isolate* isolate, Getter getter, Setter setter, Query query,
    Descriptor descriptor, Deleter remover, Enumerator enumerator,
    Definer definer, Local<Value> data, PropertyHandlerFlags flags) {
  auto interceptor =
      CreateInterceptorInfo(isolate, getter, setter, query, descriptor, remover,
                            enumerator, definer, data, flags);
  interceptor->set_is_named(false);
  return interceptor;
}

template <typename Getter, typename Setter, typename Query, typename Descriptor,
          typename Deleter, typename Enumerator, typename Definer>
static void ObjectTemplateSetNamedPropertyHandler(
    ObjectTemplate* templ, Getter getter, Setter setter, Query query,
    Descriptor descriptor, Deleter remover, Enumerator enumerator,
    Definer definer, Local<Value> data, PropertyHandlerFlags flags) {
  i::Isolate* isolate = Utils::OpenHandle(templ)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, templ);
  EnsureNotInstantiated(cons, "ObjectTemplateSetNamedPropertyHandler");
  auto obj =
      CreateNamedInterceptorInfo(isolate, getter, setter, query, descriptor,
                                 remover, enumerator, definer, data, flags);
  cons->set_named_property_handler(*obj);
}

void ObjectTemplate::SetHandler(
    const NamedPropertyHandlerConfiguration& config) {
  ObjectTemplateSetNamedPropertyHandler(
      this, config.getter, config.setter, config.query, config.descriptor,
      config.deleter, config.enumerator, config.definer, config.data,
      config.flags);
}


void ObjectTemplate::MarkAsUndetectable() {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, this);
  EnsureNotInstantiated(cons, "v8::ObjectTemplate::MarkAsUndetectable");
  cons->set_undetectable(true);
}


void ObjectTemplate::SetAccessCheckCallback(AccessCheckCallback callback,
                                            Local<Value> data) {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, this);
  EnsureNotInstantiated(cons, "v8::ObjectTemplate::SetAccessCheckCallback");

  i::Handle<i::Struct> struct_info =
      isolate->factory()->NewStruct(i::ACCESS_CHECK_INFO_TYPE, i::TENURED);
  i::Handle<i::AccessCheckInfo> info =
      i::Handle<i::AccessCheckInfo>::cast(struct_info);

  SET_FIELD_WRAPPED(isolate, info, set_callback, callback);
  info->set_named_interceptor(nullptr);
  info->set_indexed_interceptor(nullptr);

  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  info->set_data(*Utils::OpenHandle(*data));

  cons->set_access_check_info(*info);
  cons->set_needs_access_check(true);
}

void ObjectTemplate::SetAccessCheckCallbackAndHandler(
    AccessCheckCallback callback,
    const NamedPropertyHandlerConfiguration& named_handler,
    const IndexedPropertyHandlerConfiguration& indexed_handler,
    Local<Value> data) {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, this);
  EnsureNotInstantiated(
      cons, "v8::ObjectTemplate::SetAccessCheckCallbackWithHandler");

  i::Handle<i::Struct> struct_info =
      isolate->factory()->NewStruct(i::ACCESS_CHECK_INFO_TYPE, i::TENURED);
  i::Handle<i::AccessCheckInfo> info =
      i::Handle<i::AccessCheckInfo>::cast(struct_info);

  SET_FIELD_WRAPPED(isolate, info, set_callback, callback);
  auto named_interceptor = CreateNamedInterceptorInfo(
      isolate, named_handler.getter, named_handler.setter, named_handler.query,
      named_handler.descriptor, named_handler.deleter, named_handler.enumerator,
      named_handler.definer, named_handler.data, named_handler.flags);
  info->set_named_interceptor(*named_interceptor);
  auto indexed_interceptor = CreateIndexedInterceptorInfo(
      isolate, indexed_handler.getter, indexed_handler.setter,
      indexed_handler.query, indexed_handler.descriptor,
      indexed_handler.deleter, indexed_handler.enumerator,
      indexed_handler.definer, indexed_handler.data, indexed_handler.flags);
  info->set_indexed_interceptor(*indexed_interceptor);

  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  info->set_data(*Utils::OpenHandle(*data));

  cons->set_access_check_info(*info);
  cons->set_needs_access_check(true);
}

void ObjectTemplate::SetHandler(
    const IndexedPropertyHandlerConfiguration& config) {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, this);
  EnsureNotInstantiated(cons, "v8::ObjectTemplate::SetHandler");
  auto obj = CreateIndexedInterceptorInfo(
      isolate, config.getter, config.setter, config.query, config.descriptor,
      config.deleter, config.enumerator, config.definer, config.data,
      config.flags);
  cons->set_indexed_property_handler(*obj);
}

void ObjectTemplate::SetCallAsFunctionHandler(FunctionCallback callback,
                                              Local<Value> data) {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::HandleScope scope(isolate);
  auto cons = EnsureConstructor(isolate, this);
  EnsureNotInstantiated(cons, "v8::ObjectTemplate::SetCallAsFunctionHandler");
  i::Handle<i::CallHandlerInfo> obj = isolate->factory()->NewCallHandlerInfo();
  SET_FIELD_WRAPPED(isolate, obj, set_callback, callback);
  SET_FIELD_WRAPPED(isolate, obj, set_js_callback, obj->redirected_callback());
  if (data.IsEmpty()) {
    data = v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate));
  }
  obj->set_data(*Utils::OpenHandle(*data));
  cons->set_instance_call_handler(*obj);
}

int ObjectTemplate::InternalFieldCount() {
  return Utils::OpenHandle(this)->embedder_field_count();
}

void ObjectTemplate::SetInternalFieldCount(int value) {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  if (!Utils::ApiCheck(i::Smi::IsValid(value),
                       "v8::ObjectTemplate::SetInternalFieldCount()",
                       "Invalid embedder field count")) {
    return;
  }
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  if (value > 0) {
    // The embedder field count is set by the constructor function's
    // construct code, so we ensure that there is a constructor
    // function to do the setting.
    EnsureConstructor(isolate, this);
  }
  Utils::OpenHandle(this)->set_embedder_field_count(value);
}

bool ObjectTemplate::IsImmutableProto() {
  return Utils::OpenHandle(this)->immutable_proto();
}

void ObjectTemplate::SetImmutableProto() {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  Utils::OpenHandle(this)->set_immutable_proto(true);
}

// --- S c r i p t s ---


// Internally, UnboundScript is a SharedFunctionInfo, and Script is a
// JSFunction.

ScriptCompiler::CachedData::CachedData(const uint8_t* data_, int length_,
                                       BufferPolicy buffer_policy_)
    : data(data_),
      length(length_),
      rejected(false),
      buffer_policy(buffer_policy_) {}


ScriptCompiler::CachedData::~CachedData() {
  if (buffer_policy == BufferOwned) {
    delete[] data;
  }
}

bool ScriptCompiler::ExternalSourceStream::SetBookmark() { return false; }

void ScriptCompiler::ExternalSourceStream::ResetToBookmark() { UNREACHABLE(); }

ScriptCompiler::StreamedSource::StreamedSource(ExternalSourceStream* stream,
                                               Encoding encoding)
    : impl_(new i::ScriptStreamingData(stream, encoding)) {}

ScriptCompiler::StreamedSource::~StreamedSource() = default;

Local<Script> UnboundScript::BindToCurrentContext() {
  auto function_info =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = function_info->GetIsolate();
  i::Handle<i::JSFunction> function =
      isolate->factory()->NewFunctionFromSharedFunctionInfo(
          function_info, isolate->native_context());
  return ToApiHandle<Script>(function);
}

int UnboundScript::GetId() {
  auto function_info =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = function_info->GetIsolate();
  LOG_API(isolate, UnboundScript, GetId);
  i::HandleScope scope(isolate);
  i::Handle<i::Script> script(i::Script::cast(function_info->script()),
                              isolate);
  return script->id();
}


int UnboundScript::GetLineNumber(int code_pos) {
  i::Handle<i::SharedFunctionInfo> obj =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = obj->GetIsolate();
  LOG_API(isolate, UnboundScript, GetLineNumber);
  if (obj->script()->IsScript()) {
    i::Handle<i::Script> script(i::Script::cast(obj->script()), isolate);
    return i::Script::GetLineNumber(script, code_pos);
  } else {
    return -1;
  }
}


Local<Value> UnboundScript::GetScriptName() {
  i::Handle<i::SharedFunctionInfo> obj =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = obj->GetIsolate();
  LOG_API(isolate, UnboundScript, GetName);
  if (obj->script()->IsScript()) {
    i::Object* name = i::Script::cast(obj->script())->name();
    return Utils::ToLocal(i::Handle<i::Object>(name, isolate));
  } else {
    return Local<String>();
  }
}


Local<Value> UnboundScript::GetSourceURL() {
  i::Handle<i::SharedFunctionInfo> obj =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = obj->GetIsolate();
  LOG_API(isolate, UnboundScript, GetSourceURL);
  if (obj->script()->IsScript()) {
    i::Object* url = i::Script::cast(obj->script())->source_url();
    return Utils::ToLocal(i::Handle<i::Object>(url, isolate));
  } else {
    return Local<String>();
  }
}


Local<Value> UnboundScript::GetSourceMappingURL() {
  i::Handle<i::SharedFunctionInfo> obj =
      i::Handle<i::SharedFunctionInfo>::cast(Utils::OpenHandle(this));
  i::Isolate* isolate = obj->GetIsolate();
  LOG_API(isolate, UnboundScript, GetSourceMappingURL);
  if (obj->script()->IsScript()) {
    i::Object* url = i::Script::cast(obj->script())->source_mapping_url();
    return Utils::ToLocal(i::Handle<i::Object>(url, isolate));
  } else {
    return Local<String>();
  }
}


MaybeLocal<Value> Script::Run(Local<Context> context) {
  auto isolate = reinterpret_cast<i::Isolate*>(context->GetIsolate());
  TRACE_EVENT_CALL_STATS_SCOPED(isolate, "v8", "V8.Execute");
  ENTER_V8(isolate, context, Script, Run, MaybeLocal<Value>(),
           InternalEscapableScope);
  i::HistogramTimerScope execute_timer(isolate->counters()->execute(), true);
  i::AggregatingHistogramTimerScope timer(isolate->counters()->compile_lazy());
  i::TimerEventScope<i::TimerEventExecute> timer_scope(isolate);
  auto fun = i::Handle<i::JSFunction>::cast(Utils::OpenHandle(this));

  i::Handle<i::Object> receiver = isolate->global_proxy();
  Local<Value> result;
  has_pending_exception = !ToLocal<Value>(
      i::Execution::Call(isolate, fun, receiver, 0, nullptr), &result);

  RETURN_ON_FAILED_EXECUTION(Value);
  RETURN_ESCAPED(result);
}


Local<Value> ScriptOrModule::GetResourceName() {
  i::Handle<i::Script> obj = Utils::OpenHandle(this);
  i::Isolate* isolate = obj->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::Handle<i::Object> val(obj->name(), isolate);
  return ToApiHandle<Value>(val);
}

Local<PrimitiveArray> ScriptOrModule::GetHostDefinedOptions() {
  i::Handle<i::Script> obj = Utils::OpenHandle(this);
  i::Isolate* isolate = obj->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  i::Handle<i::FixedArray> val(obj->host_defined_options(), isolate);
  return ToApiHandle<PrimitiveArray>(val);
}

Local<UnboundScript> Script::GetUnboundScript() {
  i::Handle<i::Object> obj = Utils::OpenHandle(this);
  i::SharedFunctionInfo* sfi = i::JSFunction::cast(*obj)->shared();
  i::Isolate* isolate = sfi->GetIsolate();
  return ToApiHandle<UnboundScript>(i::handle(sfi, isolate));
}

// static
Local<PrimitiveArray> PrimitiveArray::New(Isolate* v8_isolate, int length) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  Utils::ApiCheck(length >= 0, "v8::PrimitiveArray::New",
                  "length must be equal or greater than zero");
  i::Handle<i::FixedArray> array = isolate->factory()->NewFixedArray(length);
  return ToApiHandle<PrimitiveArray>(array);
}

int PrimitiveArray::Length() const {
  i::Handle<i::FixedArray> array = Utils::OpenHandle(this);
  return array->length();
}

void PrimitiveArray::Set(Isolate* v8_isolate, int index,
                         Local<Primitive> item) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  i::Handle<i::FixedArray> array = Utils::OpenHandle(this);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  Utils::ApiCheck(index >= 0 && index < array->length(),
                  "v8::PrimitiveArray::Set",
                  "index must be greater than or equal to 0 and less than the "
                  "array length");
  i::Handle<i::Object> i_item = Utils::OpenHandle(*item);
  array->set(index, *i_item);
}

Local<Primitive> PrimitiveArray::Get(Isolate* v8_isolate, int index) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  i::Handle<i::FixedArray> array = Utils::OpenHandle(this);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  Utils::ApiCheck(index >= 0 && index < array->length(),
                  "v8::PrimitiveArray::Get",
                  "index must be greater than or equal to 0 and less than the "
                  "array length");
  i::Handle<i::Object> i_item(array->get(index), isolate);
  return ToApiHandle<Primitive>(i_item);
}

Module::Status Module::GetStatus() const {
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  switch (self->status()) {
    case i::Module::kUninstantiated:
    case i::Module::kPreInstantiating:
      return kUninstantiated;
    case i::Module::kInstantiating:
      return kInstantiating;
    case i::Module::kInstantiated:
      return kInstantiated;
    case i::Module::kEvaluating:
      return kEvaluating;
    case i::Module::kEvaluated:
      return kEvaluated;
    case i::Module::kErrored:
      return kErrored;
  }
  UNREACHABLE();
}

Local<Value> Module::GetException() const {
  Utils::ApiCheck(GetStatus() == kErrored, "v8::Module::GetException",
                  "Module status must be kErrored");
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  return ToApiHandle<Value>(i::handle(self->GetException(), isolate));
}

int Module::GetModuleRequestsLength() const {
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  return self->info()->module_requests()->length();
}

Local<String> Module::GetModuleRequest(int i) const {
  CHECK_GE(i, 0);
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  i::Handle<i::FixedArray> module_requests(self->info()->module_requests(),
                                           isolate);
  CHECK_LT(i, module_requests->length());
  return ToApiHandle<String>(i::handle(module_requests->get(i), isolate));
}

Location Module::GetModuleRequestLocation(int i) const {
  CHECK_GE(i, 0);
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  i::HandleScope scope(isolate);
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  i::Handle<i::FixedArray> module_request_positions(
      self->info()->module_request_positions(), isolate);
  CHECK_LT(i, module_request_positions->length());
  int position = i::Smi::ToInt(module_request_positions->get(i));
  i::Handle<i::Script> script(self->script(), isolate);
  i::Script::PositionInfo info;
  i::Script::GetPositionInfo(script, position, &info, i::Script::WITH_OFFSET);
  return v8::Location(info.line, info.column);
}

Local<Value> Module::GetModuleNamespace() {
  Utils::ApiCheck(
      GetStatus() >= kInstantiated, "v8::Module::GetModuleNamespace",
      "v8::Module::GetModuleNamespace must be used on an instantiated module");
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  i::Handle<i::JSModuleNamespace> module_namespace =
      i::Module::GetModuleNamespace(self->GetIsolate(), self);
  return ToApiHandle<Value>(module_namespace);
}

Local<UnboundModuleScript> Module::GetUnboundModuleScript() {
  Utils::ApiCheck(
      GetStatus() < kEvaluating, "v8::Module::GetUnboundScript",
      "v8::Module::GetUnboundScript must be used on an unevaluated module");
  i::Handle<i::Module> self = Utils::OpenHandle(this);
  return ToApiHandle<UnboundModuleScript>(i::Handle<i::SharedFunctionInfo>(
      self->GetSharedFunctionInfo(), self->GetIsolate()));
}

int Module::GetIdentityHash() const { return Utils::OpenHandle(this)->hash(); }

Maybe<bool> Module::InstantiateModule(Local<Context> context,
                                      Module::ResolveCallback callback) {
  auto isolate = reinterpret_cast<i::Isolate*>(context->GetIsolate());
  ENTER_V8(isolate, context, Module, InstantiateModule, Nothing<bool>(),
           i::HandleScope);
  has_pending_exception = !i::Module::Instantiate(
      isolate, Utils::OpenHandle(this), context, callback);
  RETURN_ON_FAILED_EXECUTION_PRIMITIVE(bool);
  return Just(true);
}

MaybeLocal<Value> Module::Evaluate(Local<Context> context) {
  auto isolate = reinterpret_cast<i::Isolate*>(context->GetIsolate());
  TRACE_EVENT_CALL_STATS_SCOPED(isolate, "v8", "V8.Execute");
  ENTER_V8(isolate, context, Module, Evaluate, MaybeLocal<Value>(),
           InternalEscapableScope);
  i::HistogramTimerScope execute_timer(isolate->counters()->execute(), true);
  i::AggregatingHistogramTimerScope timer(isolate->counters()->compile_lazy());
  i::TimerEventScope<i::TimerEventExecute> timer_scope(isolate);

  i::Handle<i::Module> self = Utils::OpenHandle(this);
  // It's an API error to call Evaluate before Instantiate.
  CHECK_GE(self->status(), i::Module::kInstantiated);

  Local<Value> result;
  has_pending_exception = !ToLocal(i::Module::Evaluate(isolate, self), &result);
  RETURN_ON_FAILED_EXECUTION(Value);
  RETURN_ESCAPED(result);
}

namespace {

i::Compiler::ScriptDetails GetScriptDetails(
    i::Isolate* isolate, Local<Value> resource_name,
    Local<Integer> resource_line_offset, Local<Integer> resource_column_offset,
    Local<Value> source_map_url, Local<PrimitiveArray> host_defined_options) {
  i::Compiler::ScriptDetails script_details;
  if (!resource_name.IsEmpty()) {
    script_details.name_obj = Utils::OpenHandle(*(resource_name));
  }
  if (!resource_line_offset.IsEmpty()) {
    script_details.line_offset =
        static_cast<int>(resource_line_offset->Value());
  }
  if (!resource_column_offset.IsEmpty()) {
    script_details.column_offset =
        static_cast<int>(resource_column_offset->Value());
  }
  script_details.host_defined_options = isolate->factory()->empty_fixed_array();
  if (!host_defined_options.IsEmpty()) {
    script_details.host_defined_options =
        Utils::OpenHandle(*(host_defined_options));
  }
  if (!source_map_url.IsEmpty()) {
    script_details.source_map_url = Utils::OpenHandle(*(source_map_url));
  }
  return script_details;
}

}  // namespace

MaybeLocal<UnboundScript> ScriptCompiler::CompileUnboundInternal(
    Isolate* v8_isolate, Source* source, CompileOptions options,
    NoCacheReason no_cache_reason) {
  auto isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  TRACE_EVENT_CALL_STATS_SCOPED(isolate, "v8", "V8.ScriptCompiler");
  ENTER_V8_NO_SCRIPT(isolate, v8_isolate->GetCurrentContext(), ScriptCompiler,
                     CompileUnbound, MaybeLocal<UnboundScript>(),
                     InternalEscapableScope);
  // ProduceParserCache, ProduceCodeCache, ProduceFullCodeCache and
  // ConsumeParserCache are not supported. They are present only for
  // backward compatability. All these options behave as kNoCompileOptions.
  if (options == kConsumeParserCache) {
    // We do not support parser caches anymore. Just set cached_data to
    // rejected to signal an error.
    options = kNoCompileOptions;
    source->cached_data->rejected = true;
  } else if (options == kProduceParserCache || options == kProduceCodeCache ||
             options == kProduceFullCodeCache) {
    options = kNoCompileOptions;
  }

  i::ScriptData* script_data = nullptr;
  if (options == kConsumeCodeCache) {
    DCHECK(source->cached_data);
    // ScriptData takes care of pointer-aligning the data.
    script_data = new i::ScriptData(source->cached_data->data,
                                    source->cached_data->length);
  }

  i::Handle<i::String> str = Utils::OpenHandle(*(source->source_string));
  i::Handle<i::SharedFunctionInfo> result;
  TRACE_EVENT0(TRACE_DISABLED_BY_DEFAULT("v8.compile"), "V8.CompileScript");
  i::Compiler::ScriptDetails script_details = GetScriptDetails(
      isolate, source->resource_name, source->resource_line_offset,
      source->resource_column_offset, source->source_map_url,
      source->host_defined_options);
  i::MaybeHandle<i::SharedFunctionInfo> maybe_function_info =
      i::Compiler::GetSharedFunctionInfoForScript(
          isolate, str, script_details, source->resource_options, nullptr,
          script_data, options, no_cache_reason, i::NOT_NATIVES_CODE);
  if (options == kConsumeCodeCache) {
    source->cached_data->rejected = script_data->rejected();
  }
  delete script_data;
  has_pending_exception = !maybe_function_info.ToHandle(&result);
  RETURN_ON_FAILED_EXECUTION(UnboundScript);
  RETURN_ESCAPED(ToApiHandle<UnboundScript>(result));
}

MaybeLocal<UnboundScript> ScriptCompiler::CompileUnboundScript(
    Isolate* v8_isolate, Source* source, CompileOptions options,
    NoCacheReason no_cache_reason) {
  Utils::ApiCheck(
      !source->GetResourceOptions().IsModule(),
      "v8::ScriptCompiler::CompileUnboundScript",
      "v8::ScriptCompiler::CompileModule must be used to compile modules");
  return CompileUnboundInternal(v8_isolate, source, options, no_cache_reason);
}

MaybeLocal<Script> ScriptCompiler::Compile(Local<Context> context,
                                           Source* source,
                                           CompileOptions options,
                                           NoCacheReason no_cache_reason) {
  Utils::ApiCheck(
      !source->GetResourceOptions().IsModule(), "v8::ScriptCompiler::Compile",
      "v8::ScriptCompiler::CompileModule must be used to compile modules");
  auto isolate = context->GetIsolate();
  auto maybe =
      CompileUnboundInternal(isolate, source, options, no_cache_reason);
  Local<UnboundScript> result;
  if (!maybe.ToLocal(&result)) return MaybeLocal<Script>();
  v8::Context::Scope scope(context);
  return result->BindToCurrentContext();
}

MaybeLocal<Module> ScriptCompiler::CompileModule(
    Isolate* isolate, Source* source, CompileOptions options,
    NoCacheReason no_cache_reason) {
  CHECK(options == kNoCompileOptions || options == kConsumeCodeCache);

  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);

  Utils::ApiCheck(source->GetResourceOptions().IsModule(),
                  "v8::ScriptCompiler::CompileModule",
                  "Invalid ScriptOrigin: is_module must be true");
  auto maybe =
      CompileUnboundInternal(isolate, source, options, no_cache_reason);
  Local<UnboundScript> unbound;
  if (!maybe.ToLocal(&unbound)) return MaybeLocal<Module>();

  i::Handle<i::SharedFunctionInfo> shared = Utils::OpenHandle(*unbound);
  return ToApiHandle<Module>(i_isolate->factory()->NewModule(shared));
}


class IsIdentifierHelper {
 public:
  IsIdentifierHelper() : is_identifier_(false), first_char_(true) {}

  bool Check(i::String* string) {
    i::ConsString* cons_string = i::String::VisitFlat(this, string, 0);
    if (cons_string == nullptr) return is_identifier_;
    // We don't support cons strings here.
    return false;
  }
  void VisitOneByteString(const uint8_t* chars, int length) {
    for (int i = 0; i < length; ++i) {
      if (first_char_) {
        first_char_ = false;
        is_identifier_ = unicode_cache_.IsIdentifierStart(chars[0]);
      } else {
        is_identifier_ &= unicode_cache_.IsIdentifierPart(chars[i]);
      }
    }
  }
  void VisitTwoByteString(const uint16_t* chars, int length) {
    for (int i = 0; i < length; ++i) {
      if (first_char_) {
        first_char_ = false;
        is_identifier_ = unicode_cache_.IsIdentifierStart(chars[0]);
      } else {
        is_identifier_ &= unicode_cache_.IsIdentifierPart(chars[i]);
      }
    }
  }

 private:
  bool is_identifier_;
  bool first_char_;
  i::UnicodeCache unicode_cache_;
  DISALLOW_COPY_AND_ASSIGN(IsIdentifierHelper);
};

MaybeLocal<Function> ScriptCompiler::CompileFunctionInContext(
    Local<Context> v8_context, Source* source, size_t arguments_count,
    Local<String> arguments[], size_t context_extension_count,
    Local<Object> context_extensions[], CompileOptions options,
    NoCacheReason no_cache_reason) {
  PREPARE_FOR_EXECUTION(v8_context, ScriptCompiler, CompileFunctionInContext,
                        Function);
  TRACE_EVENT_CALL_STATS_SCOPED(isolate, "v8", "V8.ScriptCompiler");

  DCHECK(options == CompileOptions::kConsumeCodeCache ||
         options == CompileOptions::kEagerCompile ||
         options == CompileOptions::kNoCompileOptions);

  i::Handle<i::Context> context = Utils::OpenHandle(*v8_context);

  DCHECK(context->IsNativeContext());
  i::Handle<i::SharedFunctionInfo> outer_info(
      context->empty_function()->shared(), isolate);

  i::Handle<i::JSFunction> fun;
  i::Handle<i::FixedArray> arguments_list =
      isolate->factory()->NewFixedArray(static_cast<int>(arguments_count));
  for (int i = 0; i < static_cast<int>(arguments_count); i++) {
    IsIdentifierHelper helper;
    i::Handle<i::String> argument = Utils::OpenHandle(*arguments[i]);
    if (!helper.Check(*argument)) return Local<Function>();
    arguments_list->set(i, *argument);
  }

  for (size_t i = 0; i < context_extension_count; ++i) {
    i::Handle<i::JSReceiver> extension =
        Utils::OpenHandle(*context_extensions[i]);
    if (!extension->IsJSObject()) return Local<Function>();
    context = isolate->factory()->NewWithContext(
        context,
        i::ScopeInfo::CreateForWithScope(
            isolate,
            context->IsNativeContext()
                ? i::Handle<i::ScopeInfo>::null()
                : i::Handle<i::ScopeInfo>(context->scope_info(), isolate)),
        extension);
  }

  i::Compiler::ScriptDetails script_details = GetScriptDetails(
      isolate, source->resource_name, source->resource_line_offset,
      source->resource_column_offset, source->source_map_url,
      source->host_defined_options);

  i::ScriptData* script_data = nullptr;
  if (options == kConsumeCodeCache) {
    DCHECK(source->cached_data);
    // ScriptData takes care of pointer-aligning the data.
    script_data = new i::ScriptData(source->cached_data->data,
                                    source->cached_data->length);
  }

  i::Handle<i::JSFunction> result;
  has_pending_exception =
      !i::Compiler::GetWrappedFunction(
           Utils::OpenHandle(*source->source_string), arguments_list, context,
           script_details, source->resource_options, script_data, options,
           no_cache_reason)
           .ToHandle(&result);
  if (options == kConsumeCodeCache) {
    source->cached_data->rejected = script_data->rejected();
  }
  delete script_data;
  RETURN_ON_FAILED_EXECUTION(Function);
  RETURN_ESCAPED(Utils::CallableToLocal(result));
}

void ScriptCompiler::ScriptStreamingTask::Run() { data_->task->Run(); }

ScriptCompiler::ScriptStreamingTask* ScriptCompiler::StartStreamingScript(
    Isolate* v8_isolate, StreamedSource* source, CompileOptions options) {
  if (!i::FLAG_script_streaming) {
    return nullptr;
  }
  // We don't support other compile options on streaming background compiles.
  // TODO(rmcilroy): remove CompileOptions from the API.
  CHECK(options == ScriptCompiler::kNoCompileOptions);
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  i::ScriptStreamingData* data = source->impl();
  std::unique_ptr<i::BackgroundCompileTask> task =
      base::make_unique<i::BackgroundCompileTask>(data, isolate);
  data->task = std::move(task);
  return new ScriptCompiler::ScriptStreamingTask(data);
}

MaybeLocal<Script> ScriptCompiler::Compile(Local<Context> context,
                                           StreamedSource* v8_source,
                                           Local<String> full_source_string,
                                           const ScriptOrigin& origin) {
  PREPARE_FOR_EXECUTION(context, ScriptCompiler, Compile, Script);
  TRACE_EVENT_CALL_STATS_SCOPED(isolate, "v8", "V8.ScriptCompiler");
  TRACE_EVENT0(TRACE_DISABLED_BY_DEFAULT("v8.compile"),
               "V8.CompileStreamedScript");

  i::Handle<i::String> str = Utils::OpenHandle(*(full_source_string));
  i::Compiler::ScriptDetails script_details = GetScriptDetails(
      isolate, origin.ResourceName(), origin.ResourceLineOffset(),
      origin.ResourceColumnOffset(), origin.SourceMapUrl(),
      origin.HostDefinedOptions());
  i::ScriptStreamingData* data = v8_source->impl();

  i::MaybeHandle<i::SharedFunctionInfo> maybe_function_info =
      i::Compiler::GetSharedFunctionInfoForStreamedScript(
          isolate, str, script_details, origin.Options(), data);

  i::Handle<i::SharedFunctionInfo> result;
  has_pending_exception = !maybe_function_info.ToHandle(&result);
  if (has_pending_exception) isolate->ReportPendingMessages();

  RETURN_ON_FAILED_EXECUTION(Script);

  Local<UnboundScript> generic = ToApiHandle<UnboundScript>(result);
  if (generic.IsEmpty()) return Local<Script>();
  Local<Script> bound = generic->BindToCurrentContext();
  if (bound.IsEmpty()) return Local<Script>();
  RETURN_ESCAPED(bound);
}

uint32_t ScriptCompiler::CachedDataVersionTag() {
  return static_cast<uint32_t>(base::hash_combine(
      internal::Version::Hash(), internal::FlagList::Hash(),
      static_cast<uint32_t>(internal::CpuFeatures::SupportedFeatures())));
}

ScriptCompiler::CachedData* ScriptCompiler::CreateCodeCache(
    Local<UnboundScript> unbound_script) {
  i::Handle<i::SharedFunctionInfo> shared =
      i::Handle<i::SharedFunctionInfo>::cast(
          Utils::OpenHandle(*unbound_script));
  DCHECK(shared->is_toplevel());
  return i::CodeSerializer::Serialize(shared);
}

// static
ScriptCompiler::CachedData* ScriptCompiler::CreateCodeCache(
    Local<UnboundModuleScript> unbound_module_script) {
  i::Handle<i::SharedFunctionInfo> shared =
      i::Handle<i::SharedFunctionInfo>::cast(
          Utils::OpenHandle(*unbound_module_script));
  DCHECK(shared->is_toplevel());
  return i::CodeSerializer::Serialize(shared);
}

ScriptCompiler::CachedData* ScriptCompiler::CreateCodeCacheForFunction(
    Local<Function> function) {
  auto js_function =
      i::Handle<i::JSFunction>::cast(Utils::OpenHandle(*function));
  i::Handle<i::SharedFunctionInfo> shared(js_function->shared(),
                                          js_function->GetIsolate());
  CHECK(shared->is_wrapped());
  return i::CodeSerializer::Serialize(shared);
}

MaybeLocal<Script> Script::Compile(Local<Context> context, Local<String> source,
                                   ScriptOrigin* origin) {
  if (origin) {
    ScriptCompiler::Source script_source(source, *origin);
    return ScriptCompiler::Compile(context, &script_source);
  }
  ScriptCompiler::Source script_source(source);
  return ScriptCompiler::Compile(context, &script_source);
}


// --- E x c e p t i o n s ---

v8::TryCatch::TryCatch(v8::Isolate* isolate)
    : isolate_(reinterpret_cast<i::Isolate*>(isolate)),
      next_(isolate_->try_catch_handler()),
      is_verbose_(false),
      can_continue_(true),
      capture_message_(true),
      rethrow_(false),
      has_terminated_(false) {
  ResetInternal();
  // Special handling for simulators which have a separate JS stack.
  js_stack_comparable_address_ =
      reinterpret_cast<void*>(i::SimulatorStack::RegisterCTryCatch(
          isolate_, i::GetCurrentStackPosition()));
  isolate_->RegisterTryCatchHandler(this);
}


v8::TryCatch::~TryCatch() {
  if (rethrow_) {
    v8::Isolate* isolate = reinterpret_cast<Isolate*>(isolate_);
    v8::HandleScope scope(isolate);
    v8::Local<v8::Value> exc = v8::Local<v8::Value>::New(isolate, Exception());
    if (HasCaught() && capture_message_) {
      // If an exception was caught and rethrow_ is indicated, the saved
      // message, script, and location need to be restored to Isolate TLS
      // for reuse.  capture_message_ needs to be disabled so that Throw()
      // does not create a new message.
      isolate_->thread_local_top()->rethrowing_message_ = true;
      isolate_->RestorePendingMessageFromTryCatch(this);
    }
    isolate_->UnregisterTryCatchHandler(this);
    i::SimulatorStack::UnregisterCTryCatch(isolate_);
    reinterpret_cast<Isolate*>(isolate_)->ThrowException(exc);
    DCHECK(!isolate_->thread_local_top()->rethrowing_message_);
  } else {
    if (HasCaught() && isolate_->has_scheduled_exception()) {
      // If an exception was caught but is still scheduled because no API call
      // promoted it, then it is canceled to prevent it from being propagated.
      // Note that this will not cancel termination exceptions.
      isolate_->CancelScheduledExceptionFromTryCatch(this);
    }
    isolate_->UnregisterTryCatchHandler(this);
    i::SimulatorStack::UnregisterCTryCatch(isolate_);
  }
}

void* v8::TryCatch::operator new(size_t) { base::OS::Abort(); }
void* v8::TryCatch::operator new[](size_t) { base::OS::Abort(); }
void v8::TryCatch::operator delete(void*, size_t) { base::OS::Abort(); }
void v8::TryCatch::operator delete[](void*, size_t) { base::OS::Abort(); }

bool v8::TryCatch::HasCaught() const {
  return !reinterpret_cast<i::Object*>(exception_)->IsTheHole(isolate_);
}


bool v8::TryCatch::CanContinue() const {
  return can_continue_;
}


bool v8::TryCatch::HasTerminated() const {
  return has_terminated_;
}


v8::Local<v8::Value> v8::TryCatch::ReThrow() {
  if (!HasCaught()) return v8::Local<v8::Value>();
  rethrow_ = true;
  return v8::Undefined(reinterpret_cast<v8::Isolate*>(isolate_));
}


v8::Local<Value> v8::TryCatch::Exception() const {
  if (HasCaught()) {
    // Check for out of memory exception.
    i::Object* exception = reinterpret_cast<i::Object*>(exception_);
    return v8::Utils::ToLocal(i::Handle<i::Object>(exception, isolate_));
  } else {
    return v8::Local<Value>();
  }
}


MaybeLocal<Value> v8::TryCatch::StackTrace(Local<Context> context) const {
  if (!HasCaught()) return v8::Local<Value>();
  i::Object* raw_obj = reinterpret_cast<i::Object*>(exception_);
  if (!raw_obj->IsJSObject()) return v8::Local<Value>();
  PREPARE_FOR_EXECUTION(context, TryCatch, StackTrace, Value);
  i::Handle<i::JSObject> obj(i::JSObject::cast(raw_obj), isolate_);
  i::Handle<i::String> name = isolate->factory()->stack_string();
  Maybe<bool> maybe = i::JSReceiver::HasProperty(obj, name);
  has_pending_exception = maybe.IsNothing();
  RETURN_ON_FAILED_EXECUTION(Value);
  if (!maybe.FromJust()) return v8::Local<Value>();
  Local<Value> result;
  has_pending_exception =
      !ToLocal<Value>(i::JSReceiver::GetProperty(isolate, obj, name), &result);
  RETURN_ON_FAILED_EXECUTION(Value);
  RETURN_ESCAPED(result);
}


v8::Local<v8::Message> v8::TryCatch::Message() const {
  i::Object* message = reinterpret_cast<i::Object*>(message_obj_);
  DCHECK(message->IsJSMessageObject() || message->IsTheHole(isolate_));
  if (HasCaught() && !message->IsTheHole(isolate_)) {
    return v8::Utils::MessageToLocal(i::Handle<i::Object>(message, isolate_));
  } else {
    return v8::Local<v8::Message>();
  }
}


void v8::TryCatch::Reset() {
  if (!rethrow_ && HasCaught() && isolate_->has_scheduled_exception()) {
    // If an exception was caught but is still scheduled because no API call
    // promoted it, then it is canceled to prevent it from being propagated.
    // Note that this will not cancel termination exceptions.
    isolate_->CancelScheduledExceptionFromTryCatch(this);
  }
  ResetInternal();
}


void v8::TryCatch::ResetInternal() {
  i::Object* the_hole = i::ReadOnlyRoots(isolate_).the_hole_value();
  exception_ = the_hole;
  message_obj_ = the_hole;
}


void v8::TryCatch::SetVerbose(bool value) {
  is_verbose_ = value;
}

bool v8::TryCatch::IsVerbose() const { return is_verbose_; }

void v8::TryCatch::SetCaptureMessage(bool value) {
  capture_message_ = value;
}


// --- M e s s a g e ---


Local<String> Message::Get() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope scope(reinterpret_cast<Isolate*>(isolate));
  i::Handle<i::Object> obj = Utils::OpenHandle(this);
  i::Handle<i::String> raw_result = i::MessageHandler::GetMessage(isolate, obj);
  Local<String> result = Utils::ToLocal(raw_result);
  return scope.Escape(result);
}

v8::Isolate* Message::GetIsolate() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  return reinterpret_cast<Isolate*>(isolate);
}

ScriptOrigin Message::GetScriptOrigin() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  auto message = i::Handle<i::JSMessageObject>::cast(Utils::OpenHandle(this));
  i::Handle<i::Script> script(message->script(), isolate);
  return GetScriptOriginForScript(isolate, script);
}


v8::Local<Value> Message::GetScriptResourceName() const {
  return GetScriptOrigin().ResourceName();
}


v8::Local<v8::StackTrace> Message::GetStackTrace() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope scope(reinterpret_cast<Isolate*>(isolate));
  auto message = i::Handle<i::JSMessageObject>::cast(Utils::OpenHandle(this));
  i::Handle<i::Object> stackFramesObj(message->stack_frames(), isolate);
  if (!stackFramesObj->IsFixedArray()) return v8::Local<v8::StackTrace>();
  auto stackTrace = i::Handle<i::FixedArray>::cast(stackFramesObj);
  return scope.Escape(Utils::StackTraceToLocal(stackTrace));
}


Maybe<int> Message::GetLineNumber(Local<Context> context) const {
  auto self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope handle_scope(reinterpret_cast<Isolate*>(isolate));
  auto msg = i::Handle<i::JSMessageObject>::cast(self);
  return Just(msg->GetLineNumber());
}


int Message::GetStartPosition() const {
  auto self = Utils::OpenHandle(this);
  return self->start_position();
}


int Message::GetEndPosition() const {
  auto self = Utils::OpenHandle(this);
  return self->end_position();
}

int Message::ErrorLevel() const {
  auto self = Utils::OpenHandle(this);
  return self->error_level();
}

int Message::GetStartColumn() const {
  auto self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope handle_scope(reinterpret_cast<Isolate*>(isolate));
  auto msg = i::Handle<i::JSMessageObject>::cast(self);
  return msg->GetColumnNumber();
}

Maybe<int> Message::GetStartColumn(Local<Context> context) const {
  return Just(GetStartColumn());
}

int Message::GetEndColumn() const {
  auto self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope handle_scope(reinterpret_cast<Isolate*>(isolate));
  auto msg = i::Handle<i::JSMessageObject>::cast(self);
  const int column_number = msg->GetColumnNumber();
  if (column_number == -1) return -1;
  const int start = self->start_position();
  const int end = self->end_position();
  return column_number + (end - start);
}

Maybe<int> Message::GetEndColumn(Local<Context> context) const {
  return Just(GetEndColumn());
}


bool Message::IsSharedCrossOrigin() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  return Utils::OpenHandle(this)
      ->script()
      ->origin_options()
      .IsSharedCrossOrigin();
}

bool Message::IsOpaque() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  return Utils::OpenHandle(this)->script()->origin_options().IsOpaque();
}


MaybeLocal<String> Message::GetSourceLine(Local<Context> context) const {
  auto self = Utils::OpenHandle(this);
  i::Isolate* isolate = self->GetIsolate();
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope handle_scope(reinterpret_cast<Isolate*>(isolate));
  auto msg = i::Handle<i::JSMessageObject>::cast(self);
  RETURN_ESCAPED(Utils::ToLocal(msg->GetSourceLine()));
}


void Message::PrintCurrentStackTrace(Isolate* isolate, FILE* out) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  i_isolate->PrintCurrentStackTrace(out);
}


// --- S t a c k T r a c e ---

Local<StackFrame> StackTrace::GetFrame(Isolate* v8_isolate,
                                       uint32_t index) const {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(isolate);
  EscapableHandleScope scope(v8_isolate);
  auto obj = handle(Utils::OpenHandle(this)->get(index), isolate);
  auto info = i::Handle<i::StackFrameInfo>::cast(obj);
  return scope.Escape(Utils::StackFrameToLocal(info));
}

int StackTrace::GetFrameCount() const {
  return Utils::OpenHandle(this)->length();
}


Local<StackTrace> StackTrace::CurrentStackTrace(
    Isolate* isolate,
    int frame_limit,
    StackTraceOptions options) {
  i::Isolate* i_isolate = reinterpret_cast<i::Isolate*>(isolate);
  ENTER_V8_NO_SCRIPT_NO_EXCEPTION(i_isolate);
  i::Handle<i::FixedArray> stackTrace =
      i_isolate->CaptureCurrentStackTrace(frame_limit, options);
  return Utils::StackTraceToLocal(stackTrace);
}


// --- S t a c k F r a m e ---

int StackFrame::GetLineNumber() const {
  int v = Utils::OpenHandle(this)->line_number();
  return v ? v : Message::kNoLineNumberInfo;
}


int StackFrame::GetColumn() const {
  int v = Utils::OpenHandle(this)->column_number();
  return v ? v : Message::kNoLineNumberInfo;
}


int StackFrame::GetScriptId() const {
  int v = Utils::OpenHandle(this)->script_id();
  return v ? v : Message::kNoScriptIdInfo;
}

Local<String> StackFrame::GetScriptName() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  EscapableHandleScope scope(reinterpret_cast<Isolate*>(isolate));
  i::Handle<i::StackFrameInfo> self = Utils::OpenHandle(this);
  i::Handle<i::Object> obj(self->script_name(), isolate);
  return obj->IsString()
             ? scope.Escape(Local<String>::Cast(Utils::ToLocal(obj)))
             : Local<String>();
}


Local<String> StackFrame::GetScriptNameOrSourceURL() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  EscapableHandleScope scope(reinterpret_cast<Isolate*>(isolate));
  i::Handle<i::StackFrameInfo> self = Utils::OpenHandle(this);
  i::Handle<i::Object> obj(self->script_name_or_source_url(), isolate);
  return obj->IsString()
             ? scope.Escape(Local<String>::Cast(Utils::ToLocal(obj)))
             : Local<String>();
}


Local<String> StackFrame::GetFunctionName() const {
  i::Isolate* isolate = Utils::OpenHandle(this)->GetIsolate();
  EscapableHandleScope scope(reinterpret_cast<Isolate*>(isolate));
  i::Handle<i::StackFrameInfo> self = Utils::OpenHandle(this);
  i::Handle<i::Object> obj(self->function_name(), isolate);
  return obj->IsString()
             ? scope.Escape(Local<String>::Cast(Utils::ToLocal(obj)))
             : Local<String>();
}

bool StackFrame::IsEval() const { return Utils::OpenHandle(this)->is_eval(); }

bool StackFrame::IsConstructor() const {
  return Utils::OpenHandle(this)->is_constructor();
}

bool StackFrame::IsWasm() const { return Utils::OpenHandle(this)->is_wasm(); }


// --- J S O N ---

MaybeLocal<Value> JSON::Parse(Isolate* v8_isolate, Local<String> json_string) {
  PREPARE_FOR_EXECUTION(v8_isolate->GetCurrentContext(), JSON, Parse, Value);
  i::Handle<i::String> string = Utils::OpenHandle(*json_string);
  i::Handle<i::String> source = i::String::Flatten(isolate, string);
  i::Handle<i::Object> undefined = isolate->factory()->undefined_value();
  auto maybe = source->IsSeqOneByteString()
                   ? i::JsonParser<true>::Parse(isolate, source, undefined)
                   : i::JsonParser<false>::Parse(isolate, source, undefined);
  Local<Value> result;
  has_pending_exception = !ToLocal<Value>(maybe, &result);
  RETURN_ON_FAILED_EXECUTION(Value);
  RETURN_ESCAPED(result);
}

MaybeLocal<Value> JSON::Parse(Local<Context> context,
                              Local<String> json_string) {
  PREPARE_FOR_EXECUTION(context, JSON, Parse, Value);
  i::Handle<i::String> string = Utils::OpenHandle(*json_string);
  i::Handle<i::String> source = i::String::Flatten(isolate, string);
  i::Handle<i::Object> undefined = isolate->factory()->undefined_value();
  auto maybe = source->IsSeqOneByteString()
                   ? i::JsonParser<true>::Parse(isolate, source, undefined)
                   : i::JsonParser<false>::Parse(isolate, source, undefined);
  Local<Value> result;
  has_pending_exception = !ToLocal<Value>(maybe, &result);
  RETURN_ON_FAILED_EXECUTION(Value);
  RETURN_ESCAPED(result);
}

MaybeLocal<String> JSON::Stringify(Local<Context> context,
                                   Local<Value> json_object,
                                   Local<String> gap) {
  PREPARE_FOR_EXECUTION(context, JSON, Stringify, String);
  i::Handle<i::Object> object = Utils::OpenHandle(*json_object);
  i::Handle<i::Object> replacer = isolate->factory()->undefined_value();
  i::Handle<i::String> gap_string = gap.IsEmpty()
                                        ? isolate->factory()->empty_string()
                                        : Utils::OpenHandle(*gap);
  i::Handle<i::Object> maybe;
  has_pending_exception =
      !i::JsonStringify(isolate, object, replacer, gap_string).ToHandle(&maybe);
  RETURN_ON_FAILED_EXECUTION(String);
  Local<String> result;
  has_pending_exception =
      !ToLocal<String>(i::Object::ToString(isolate, maybe), &result);
  RETURN_ON_FAILED_EXECUTION(String);
  RETURN_ESCAPED(result);
}

// --- V a l u e   S e r i a l i z a t i o n ---

Maybe<bool> ValueSerializer::Delegate::WriteHostObject(Isolate* v8_isolate,
                                                       Local<Object> object) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  isolate->ScheduleThrow(*isolate->factory()->NewError(
      isolate->error_function(), i::MessageTemplate::kDataCloneError,
      Utils::OpenHandle(*object)));
  return Nothing<bool>();
}

Maybe<uint32_t> ValueSerializer::Delegate::GetSharedArrayBufferId(
    Isolate* v8_isolate, Local<SharedArrayBuffer> shared_array_buffer) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  isolate->ScheduleThrow(*isolate->factory()->NewError(
      isolate->error_function(), i::MessageTemplate::kDataCloneError,
      Utils::OpenHandle(*shared_array_buffer)));
  return Nothing<uint32_t>();
}

Maybe<uint32_t> ValueSerializer::Delegate::GetWasmModuleTransferId(
    Isolate* v8_isolate, Local<WasmCompiledModule> module) {
  return Nothing<uint32_t>();
}

void* ValueSerializer::Delegate::ReallocateBufferMemory(void* old_buffer,
                                                        size_t size,
                                                        size_t* actual_size) {
  *actual_size = size;
  return realloc(old_buffer, size);
}

void ValueSerializer::Delegate::FreeBufferMemory(void* buffer) {
  return free(buffer);
}

struct ValueSerializer::PrivateData {
  explicit PrivateData(i::Isolate* i, ValueSerializer::Delegate* delegate)
      : isolate(i), serializer(i, delegate) {}
  i::Isolate* isolate;
  i::ValueSerializer serializer;
};

ValueSerializer::ValueSerializer(Isolate* isolate)
    : ValueSerializer(isolate, nullptr) {}

ValueSerializer::ValueSerializer(Isolate* isolate, Delegate* delegate)
    : private_(
          new PrivateData(reinterpret_cast<i::Isolate*>(isolate), delegate)) {}

ValueSerializer::~ValueSerializer() { delete private_; }

void ValueSerializer::WriteHeader() { private_->serializer.WriteHeader(); }

void ValueSerializer::SetTreatArrayBufferViewsAsHostObjects(bool mode) {
  private_->serializer.SetTreatArrayBufferViewsAsHostObjects(mode);
}

Maybe<bool> ValueSerializer::WriteValue(Local<Context> context,
                                        Local<Value> value) {
  auto isolate = reinterpret_cast<i::Isolate*>(context->GetIsolate());
  ENTER_V8(isolate, context, ValueSerializer, WriteValue, Nothing<bool>(),
           i::HandleScope);
  i::Handle<i::Object> object = Utils::OpenHandle(*value);
  Maybe<bool> result = private_->serializer.WriteObject(object);
  has_pending_exception = result.IsNothing();
  RETURN_ON_FAILED_EXECUTION_PRIMITIVE(bool);
  return result;
}

std::vector<uint8_t> ValueSerializer::ReleaseBuffer() {
  return private_->serializer.ReleaseBuffer();
}

std::pair<uint8_t*, size_t> ValueSerializer::Release() {
  return private_->serializer.Release();
}

void ValueSerializer::TransferArrayBuffer(uint32_t transfer_id,
                                          Local<ArrayBuffer> array_buffer) {
  private_->serializer.TransferArrayBuffer(transfer_id,
                                           Utils::OpenHandle(*array_buffer));
}

void ValueSerializer::TransferSharedArrayBuffer(
    uint32_t transfer_id, Local<SharedArrayBuffer> shared_array_buffer) {
  private_->serializer.TransferArrayBuffer(
      transfer_id, Utils::OpenHandle(*shared_array_buffer));
}

void ValueSerializer::WriteUint32(uint32_t value) {
  private_->serializer.WriteUint32(value);
}

void ValueSerializer::WriteUint64(uint64_t value) {
  private_->serializer.WriteUint64(value);
}

void ValueSerializer::WriteDouble(double value) {
  private_->serializer.WriteDouble(value);
}

void ValueSerializer::WriteRawBytes(const void* source, size_t length) {
  private_->serializer.WriteRawBytes(source, length);
}

MaybeLocal<Object> ValueDeserializer::Delegate::ReadHostObject(
    Isolate* v8_isolate) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  isolate->ScheduleThrow(*isolate->factory()->NewError(
      isolate->error_function(),
      i::MessageTemplate::kDataCloneDeserializationError));
  return MaybeLocal<Object>();
}

MaybeLocal<WasmCompiledModule> ValueDeserializer::Delegate::GetWasmModuleFromId(
    Isolate* v8_isolate, uint32_t id) {
  i::Isolate* isolate = reinterpret_cast<i::Isolate*>(v8_isolate);
  isolate->ScheduleThrow(*isolate->factory()->NewError(
      isolate->error_function(),
      i::MessageTemplate::kDataCloneDeserializationError));
  return MaybeLocal<WasmCompiledModule>();
}


#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/rtems/status.h>
#include <rtems/score/fmlpl.h>
#include <rtems/score/dpcp.h>
#include <rtems/score/scheduler.h>
#include <rtems/rtems/tasksdata.h>
#include "common_contracts.h"
/************************************************/

//                LOGIC FUNCTION

/************************************************/
/*@
  logic Thread_Control* FMLPLMutex_Owner(FMLPL_Control *m) =
    m->Wait_queue.Queue.owner;
 */
/************************************************/

//      FUNCTIONS CONSIDERED FOR FMLP-L

/************************************************/
/*@
   requires \valid(fmlpl) && \valid(queue_context);
   assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPL_Acquire_critical(
  FMLPL_Control        *fmlpl,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(executing) && \valid(queue_context);
  requires fmlpl->first_free_slot >=0;
  requires 0<fmlpl->first_free_slot<15;
  assigns fmlpl->first_free_slot,fmlpl->priority_array[fmlpl->first_free_slot];
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_add(
  FMLPL_Control        *fmlpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl);
  assigns \nothing;
  ensures FMLPLMutex_Owner(fmlpl)==NULL ==> \result == STATUS_SUCCESSFUL;
  ensures FMLPLMutex_Owner(fmlpl)!=NULL ==> \result == STATUS_RESOURCE_IN_USE;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Can_destroy(
  FMLPL_Control *fmlpl
);
/*@
  requires \valid(fmlpl);
  assigns \nothing;
  ensures \result == FMLPLMutex_Owner(fmlpl);
 */
RTEMS_INLINE_ROUTINE Thread_Control *_FMLPL_Get_owner(
  const FMLPL_Control *fmlpl
);
/*@
  requires \valid(fmlpl);
  assigns fmlpl->Wait_queue.Queue.owner;
  ensures FMLPLMutex_Owner(fmlpl) == \old(owner);
 */
RTEMS_INLINE_ROUTINE void _FMLPL_Set_owner(
  FMLPL_Control  *fmlpl,
  Thread_Control *owner
);
/*
  requires \valid(fmlpl);
  assigns fmlpl->Wait_queue.Queue.owner;
  ensures FMLPLMutex_Owner(fmlpl) == NULL;
 */
RTEMS_INLINE_ROUTINE void _FMLPL_Set_empty_owner(
  FMLPL_Control  *fmlpl
);
/*@
  requires \valid(fmlpl) && \valid(queue_context);
  assigns \nothing;
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Change_Owner_Priority(
  Priority_Control      new_prio,
  FMLPL_Control        *fmlpl,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(queue_context) && \valid(executing);
  requires fmlpl->first_free_slot >=0;
  assigns fmlpl->Wait_queue.Queue.owner;
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Claim_ownership(
  FMLPL_Control        *fmlpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPL_Release(
  FMLPL_Control        *fmlpl,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE Priority_Control _FMLPL_Get_Min_Priority(
  FMLPL_Control *fmlpl
);
/*@
  requires \valid(fmlpl) ∧ \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPL_Destroy(
  FMLPL_Control        *fmlpl,
  Thread_queue_Context *queue_context
);
/*@
  requires 0<fmlpl->first_free_slot<15;
  requires \valid(fmlpl);
  assigns fmlpl->first_free_slot,fmlpl->priority_array[fmlpl->first_free_slot],fmlpl->priority_array[0 .. 16];
  behavior negSlotNum:
   assumes fmlpl->first_free_slot < 0;
   ensures \result == 1;
  behavior maxSlotNum:
   assumes fmlpl->first_free_slot > 15;
   ensures \result == 1;
  behavior busySlotNum:
   assumes fmlpl->priority_array[fmlpl->first_free_slot] != 0 ;
   ensures \result == 1;
  behavior else:
   assumes fmlpl->first_free_slot > 0 && fmlpl->first_free_slot < 15
    && fmlpl->priority_array[fmlpl->first_free_slot] == 0 ;
    ensures \result == 0;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_remove(
  FMLPL_Control *fmlpl
);
/*@
  requires 0<fmlpl->first_free_slot<15;
  requires \valid(fmlpl) && \valid(executing);
  assigns fmlpl->first_free_slot,fmlpl->priority_array[fmlpl->first_free_slot];
  behavior negSlotNum:
   assumes fmlpl->first_free_slot < 0;
   ensures \result == 1;
  behavior maxSlotNum:
   assumes fmlpl->first_free_slot > 15;
   ensures \result == 1;
  behavior busySlotNum:
   assumes fmlpl->priority_array[fmlpl->first_free_slot] != 0 ;
   ensures \result == 1;
  behavior else:
   assumes fmlpl->first_free_slot > 0 && fmlpl->first_free_slot < 15
    && fmlpl->priority_array[fmlpl->first_free_slot] == 0 ;
    ensures \result == 0;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Insert(
  FMLPL_Control  *fmlpl,
  Thread_Control *executing
);
/*@
  requires \valid(the_thread);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE Priority_Control _FMLPL_Get_priority(
  const Thread_Control *the_thread
);
/*@
  requires \valid(fmlpl) && \valid(executing)&& \valid(queue_context);
  requires fmlpl->first_free_slot ≥ 0;
     requires 0 < fmlpl->first_free_slot < 15;
  assigns fmlpl->Wait_queue.Queue.owner;
  behavior notOwner:
   assumes FMLPLMutex_Owner(fmlpl) != executing;
   ensures \result == STATUS_NOT_OWNER;
  behavior noHeads:
   assumes fmlpl->Wait_queue.Queue.heads == NULL && FMLPLMutex_Owner(fmlpl) == executing;
   ensures \result == RTEMS_SUCCESSFUL;
  behavior headsOwner:
   assumes fmlpl->Wait_queue.Queue.heads != NULL && FMLPLMutex_Owner(fmlpl) == executing;
   ensures \result == RTEMS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Surrender(
  FMLPL_Control        *fmlpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(executing)&& \valid(queue_context);
  requires fmlpl->first_free_slot >=0;
  requires 0<fmlpl->first_free_slot<15; //wait for owner
  behavior noOwner:
   assumes FMLPLMutex_Owner(fmlpl) == NULL;
   assigns fmlpl->Wait_queue.Queue.owner;
   ensures \result == RTEMS_SUCCESSFUL;
  behavior ownerExecuting:
   assumes FMLPLMutex_Owner(fmlpl) != NULL && FMLPLMutex_Owner(fmlpl) == executing;
   ensures \result == STATUS_UNAVAILABLE;
  behavior waitForOwner:
   assumes FMLPLMutex_Owner(fmlpl) != NULL && FMLPLMutex_Owner(fmlpl) != executing && wait;
   ensures \result == RTEMS_SUCCESSFUL;
  behavior else:
   assumes FMLPLMutex_Owner(fmlpl) != NULL && FMLPLMutex_Owner(fmlpl) != executing && !wait;
   ensures \result == STATUS_UNAVAILABLE;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Seize(
  FMLPL_Control        *fmlpl,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(executing) && \valid(queue_context);
  requires fmlpl->first_free_slot >=0;
  requires 0<fmlpl->first_free_slot<15;
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Wait_for_ownership(
  FMLPL_Control        *fmlpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlpl) && \valid(scheduler) && \valid(executing);
  ensures initially_locked ==> \result == STATUS_INVALID_NUMBER;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPL_Initialize(
  FMLPL_Control           *fmlpl,
  const Scheduler_Control *scheduler,
  Priority_Control         ceiling_priority,
  Thread_Control          *executing,
  bool                     initially_locked
);
/************************************************/

// LOWER LAYER FUNCTIONS ABSTRACTED IN FMLP-L

/************************************************/
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE rtems_task_priority _RTEMS_Priority_From_core(
  const Scheduler_Control *scheduler,
  Priority_Control         priority
);
//@ assigns \nothing;
void _Thread_Priority_add(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
void _Thread_Priority_remove(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
void _Thread_Priority_update( Thread_queue_Context *queue_context );

//@ assigns \nothing;
void _Thread_queue_Surrender(
  Thread_queue_Queue            *queue,
  Thread_queue_Heads            *heads,
  Thread_Control                *previous_owner,
  Thread_queue_Context          *queue_context,
  const Thread_queue_Operations *operations
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void
_Thread_queue_Context_set_enqueue_do_nothing_extra(
  Thread_queue_Context *queue_context
);
// bypass inline assembler
#define _ISR_lock_ISR_enable(_context) (void) _context;
//@ assigns \nothing;
void *_Workspace_Allocate( size_t size );

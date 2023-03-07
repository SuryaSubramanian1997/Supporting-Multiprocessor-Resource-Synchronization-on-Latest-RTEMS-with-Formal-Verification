#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/rtems/status.h>
#include <rtems/score/dflpl.h>
#include <rtems/score/dpcp.h>
#include <rtems/score/scheduler.h>
#include <rtems/score/schedulerimpl.h>
#include "common_contracts.h"
/************************************************/

//                LOGIC FUNCTION

/************************************************/
/*@
  logic Thread_Control* DFLPLMutex_Owner(DFLPL_Control *m) =
    m->Wait_queue.Queue.owner;
 */
/************************************************/

//      FUNCTIONS CONSIDERED FOR DFLPL

/************************************************/
/*@
  requires \valid(dflpl); //&& \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _DFLPL_Acquire_critical(
  DFLPL_Control        *dflpl,
  Thread_queue_Context *queue_context
);
//@assigns \nothing;
RTEMS_INLINE_ROUTINE void _DFLPL_Release(
  DFLPL_Control        *dflpl,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dflpl) && \valid(cpu) && \valid(queue_context);
  assigns dflpl->pu;
  ensures dflpl->pu == cpu;
 */
RTEMS_INLINE_ROUTINE void _DFLPL_Set_CPU(
  DFLPL_Control        *dflpl,
  Per_CPU_Control      *cpu,
  Thread_queue_Context *queue_context
);
/*@
  assigns \nothing;
  ensures \result == DFLPLMutex_Owner(dflpl);
 */
RTEMS_INLINE_ROUTINE Thread_Control *_DFLPL_Get_owner(
  const DFLPL_Control *dflpl
);
/*@
  requires \valid(dflpl);
  assigns dflpl->Wait_queue.Queue.owner;
  ensures DFLPLMutex_Owner(dflpl) == owner;
 */
RTEMS_INLINE_ROUTINE void _DFLPL_Set_owner(
  DFLPL_Control  *dflpl,
  Thread_Control *owner
);
/*@
  requires \valid(dflpl);
  assigns dflpl->Wait_queue.Queue.owner;
  ensures DFLPLMutex_Owner(dflpl) == NULL;
 */
RTEMS_INLINE_ROUTINE void _DFLPL_Set_owner_null(
  DFLPL_Control  *dflpl
);
/*@
  requires \valid(dflpl) && \valid(executing)&& \valid(queue_context);
  requires 0 < dflpl->first_free_slot < 15;
  assigns dflpl->Wait_queue.Queue.owner;
  behavior notOwner:
   assumes DFLPLMutex_Owner(dflpl) != executing;
   ensures \result == STATUS_NOT_OWNER;
  behavior noHeads:
   assumes dflpl->Wait_queue.Queue.heads == NULL && DFLPLMutex_Owner(dflpl) == executing;
   ensures \result == RTEMS_SUCCESSFUL;
  behavior headsOwner:
   assumes dflpl->Wait_queue.Queue.heads != NULL && DFLPLMutex_Owner(dflpl) == executing;
   ensures \result == STATUS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Surrender(
  DFLPL_Control        *dflpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dflpl) && \valid(executing)&& \valid(queue_context);
  requires 0<dflpl->first_free_slot<15;
  requires dflpl->first_free_slot >=0;
  behavior noOwner:
   assumes DFLPLMutex_Owner(dflpl) == NULL;
   ensures \result == STATUS_SUCCESSFUL;
  behavior ownerExec:
   assumes DFLPLMutex_Owner(dflpl) != NULL && DFLPLMutex_Owner(dflpl) == executing;
   ensures \result == STATUS_UNAVAILABLE;
  behavior waitForOwner:
   assumes DFLPLMutex_Owner(dflpl) != NULL && DFLPLMutex_Owner(dflpl) != executing && wait;
   ensures \result == STATUS_SUCCESSFUL;
  behavior else:
   assumes DFLPLMutex_Owner(dflpl) != NULL && DFLPLMutex_Owner(dflpl) != executing && !wait;
   ensures \result == STATUS_UNAVAILABLE;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Seize(
  DFLPL_Control        *dflpl,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dflpl) && \valid(executing) && \valid(queue_context);
  requires 0<dflpl->first_free_slot<15;
  requires dflpl->first_free_slot >=0;
  ensures \result == STATUS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Wait_for_ownership(
  DFLPL_Control        *dflpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dflpl) && \valid(executing) && \valid(queue_context);
  assigns dflpl->Wait_queue.Queue.owner;
  ensures \result == STATUS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Claim_ownership(
  DFLPL_Control        *dflpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dflpl);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE Priority_Control _DFLPL_Get_Min_Priority(
  DFLPL_Control *dflpl
);
/*@
  requires \valid(dflpl) && \valid(executing) && \valid(queue_context);
  requires dflpl->first_free_slot >=0; //get_min_priority
  requires 0<dflpl->first_free_slot<15; //add
  assigns dflpl->first_free_slot,dflpl->priority_array[dflpl->first_free_slot];
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_add(
  DFLPL_Control        *dflpl,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires 0<dflpl->first_free_slot<15;
  requires \valid(executing);
  requires dflpl->first_free_slot >=0; //get_min_priority
  assigns dflpl->first_free_slot,dflpl->priority_array[dflpl->first_free_slot];
  behavior negSlotNum:
   assumes dflpl->first_free_slot < 0;
   ensures \result == 1;
  behavior maxSlotNum:
   assumes dflpl->first_free_slot > 15;
   ensures \result == 1;
  behavior busySlotNum:
   assumes dflpl->priority_array[dflpl->first_free_slot] != 0 ;
   ensures \result == 1;
  behavior else:
   assumes dflpl->first_free_slot > 0 && dflpl->first_free_slot < 15
    && dflpl->priority_array[dflpl->first_free_slot] == 0 ;
    ensures \result == 0;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Insert(
  DFLPL_Control  *dflpl,
  Thread_Control *executing
);
/*@
  requires 0<dflpl->first_free_slot<15;
  requires \valid(dflpl);
  behavior negSlotNum:
   assumes dflpl->first_free_slot < 0;
   assigns \nothing;
   ensures \result == 1;
  behavior maxSlotNum:
   assumes dflpl->first_free_slot > 15;
   assigns \nothing;
   ensures \result == 1;
  behavior busySlotNum:
   assumes dflpl->priority_array[dflpl->first_free_slot] != 0 ;
   assigns \nothing;
   ensures \result == 1;
  behavior else:
   assumes dflpl->first_free_slot > 0 && dflpl->first_free_slot < 15
    && dflpl->priority_array[dflpl->first_free_slot] == 0 ;
    assigns dflpl->first_free_slot,dflpl->priority_array[0 .. dflpl->first_free_slot];
    ensures \result == 0;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_remove(
  DFLPL_Control *dflpl
);
/*@
  requires \valid(the_thread);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE Priority_Control _DFLPL_Get_priority(
  const Thread_Control *the_thread
);
/*@
  assigns \nothing;
  ensures \result == RTEMS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Change_Owner_Priority(
  Thread_Control       *executing,
  Priority_Control      new_prio,
  DFLPL_Control        *dflpl,
  Thread_queue_Context *queue_context
);
/*@
  assigns \nothing;
  ensures DFLPLMutex_Owner(dflpl) != NULL ==> \result == STATUS_RESOURCE_IN_USE;
  ensures DFLPLMutex_Owner(dflpl) == NULL ==> \result == STATUS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Can_destroy(
  DFLPL_Control *dflpl
);
//@    assigns \nothing;
RTEMS_INLINE_ROUTINE void _DFLPL_Migrate(
    Thread_Control *executing,
    DFLPL_Control  *dflpl,
    Priority_Node  *migration_priority
);
//@    assigns \nothing;
RTEMS_INLINE_ROUTINE void _DFLPL_Migrate_Back(
  Thread_Control *executing,
  DFLPL_Control  *dflpl
);
//@  requires \valid(dflpl) && \valid(scheduler) && \valid(executing);
RTEMS_INLINE_ROUTINE Status_Control _DFLPL_Initialize(
  DFLPL_Control           *dflpl,
  const Scheduler_Control *scheduler,
  Priority_Control         ceiling_priority,
  Thread_Control          *executing,
  bool                     initially_locked
);
/************************************************************/

//		LOWER LAYER FUNCTIONS ABSTRACTED FOR DFLPL

/************************************************************/
// bypass inline assembler
#define _ISR_lock_ISR_enable(_context) (void) _context;
//@    assigns \nothing;
RTEMS_INLINE_ROUTINE void _Scheduler_Change_migration_priority(
          Thread_Control  *executing,
          Per_CPU_Control *migration_cpu,
          Priority_Node   *priority
        );
//@    assigns \nothing;
void _Thread_queue_Surrender_and_Migrate(
  Thread_queue_Queue            *queue,
  Thread_queue_Heads            *heads,
  Thread_Control                *previous_owner,
  Thread_queue_Context          *queue_context,
  const Thread_queue_Operations *operations,
  Per_CPU_Control *cpu,
  Priority_Node *priority
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_Back(
          Thread_Control  *executing,
          Per_CPU_Control *migration_cpu
        );
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_To(
          Thread_Control  *executing,
          Per_CPU_Control *migration_cpu,
          Priority_Node   *ceiling_priority
        );
//@ assigns \nothing;
void _Thread_queue_Enqueue2(Thread_queue_Queue *queue,
                            Thread_queue_Operations const *operations,
                            Thread_Control *the_thread,
                            Thread_queue_Context *queue_context,
                            Per_CPU_Control *cpu);
//@ assigns \nothing;
static void _Thread_queue_Context_set_enqueue_do_nothing_extra
(Thread_queue_Context *queue_context);

//@ assigns \nothing;
static void _Thread_queue_Context_set_deadlock_callout(Thread_queue_Context *queue_context,
                                                       void (*deadlock_callout)
                                                       (Thread_Control *the_thread));

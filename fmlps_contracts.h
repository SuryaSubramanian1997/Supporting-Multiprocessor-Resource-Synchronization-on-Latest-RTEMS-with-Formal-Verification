#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/rtems/status.h>
#include <rtems/score/fmlpl.h>
#include <rtems/score/fmlps.h>
#include <rtems/score/dpcp.h>
#include <rtems/score/scheduler.h>
#include <rtems/rtems/tasksdata.h>
#include "common_contracts.h"
/************************************************/

//	 GHOST VARIABLE(S)

/************************************************/
/*@ ghost
   extern Status_Control g_status;
   extern uint32_t g_scheduler_index;
   extern Scheduler_Node *g_homenode;
 */
/************************************************/

//      LOGIC FUNCTIONS AND PREDICATES

/************************************************/
/*@
  logic Thread_Control* FMLPSMutex_Owner(FMLPS_Control *m) =
    m->Wait_queue.Queue.owner;
  logic Priority_Control get_Priority(Priority_Aggregation *a) =
    a->Node.priority;
  logic Priority_Control fmlpsCurrentPriority(FMLPS_Control *f) =
    f->ceiling_priorities[g_scheduler_index];
  logic Priority_Control homeSchedulerPriority =
    get_Priority(&g_homenode->Wait.Priority);
  predicate isFMLPSOwnerEmpty(FMLPS_Control *f) =
  	f->Wait_queue.Queue.owner == NULL;
 */
/************************************************/

//      FUNCTIONS CONSIDERED FOR FMLP-S

/************************************************/
/*@
  requires \valid(fmlps);
  assigns \nothing;
  ensures isFMLPSOwnerEmpty(fmlps) ==> \result == STATUS_SUCCESSFUL;
  ensures !isFMLPSOwnerEmpty(fmlps)==> \result == STATUS_RESOURCE_IN_USE;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Can_destroy( FMLPS_Control *fmlps );
/*@
  requires \valid(fmlps) && \valid(queue_context) && \valid(executing);
  assigns fmlps->Wait_queue.Queue.owner;
  ensures \result == STATUS_SUCCESSFUL || \result == STATUS_MUTEX_CEILING_VIOLATED;
  ensures ( homeSchedulerPriority >= fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_SUCCESSFUL);
  ensures ( homeSchedulerPriority < fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_MUTEX_CEILING_VIOLATED);
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Claim_ownership(
  FMLPS_Control        *fmlps,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlps) && \valid(thread) && \valid(priority_node)&& \valid(queue_context) ;
  assigns \nothing;
  ensures \result == STATUS_SUCCESSFUL || \result == STATUS_MUTEX_CEILING_VIOLATED;
  ensures ( homeSchedulerPriority >= fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_SUCCESSFUL);
  ensures ( homeSchedulerPriority < fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_MUTEX_CEILING_VIOLATED);
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Raise_priority(
  FMLPS_Control        *fmlps,
  Thread_Control       *thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlps) && \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPS_Acquire_critical(
  FMLPS_Control        *fmlps,
  Thread_queue_Context *queue_context
);
/*@
  requires _Scheduler_Count>=0;
  //assigns fmlps->ceiling_priorities,fmlps->ceiling_priorities[0 .. 16];
  ensures initially_locked ==> \result == STATUS_INVALID_NUMBER;
  ensures fmlps->ceiling_priorities == NULL && !initially_locked  ==> \result == STATUS_NO_MEMORY;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Initialize(
  FMLPS_Control           *fmlps,
  const Scheduler_Control *scheduler,
  Priority_Control         ceiling_priority,
  Thread_Control          *executing,
  bool                     initially_locked
);
/*@
  requires \valid(fmlps);
  assigns fmlps->Wait_queue.Queue.owner;
  ensures fmlps->Wait_queue.Queue.owner==owner;
 */
RTEMS_INLINE_ROUTINE void _FMLPS_Set_owner(
  FMLPS_Control  *fmlps,
  Thread_Control *owner
);
/*@
  requires \valid(fmlps);
  assigns \nothing;
  ensures \result == FMLPSMutex_Owner(fmlps);
 */
RTEMS_INLINE_ROUTINE Thread_Control *_FMLPS_Get_owner(
  const FMLPS_Control *fmlps
);
/*@
  requires \valid(fmlps) && \valid(executing)&& \valid(queue_context);
  requires g_status != 0;
  assigns fmlps->Wait_queue.Queue.owner;
  assigns queue_context->deadlock_callout; // wait for owner
  behavior claimOwnership:
   assumes isFMLPSOwnerEmpty(fmlps);
   ensures \result == STATUS_SUCCESSFUL || \result == STATUS_MUTEX_CEILING_VIOLATED;
   ensures ( homeSchedulerPriority >= fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_SUCCESSFUL);
  ensures ( homeSchedulerPriority < fmlpsCurrentPriority( fmlps )
  ==> \result == STATUS_MUTEX_CEILING_VIOLATED);
  behavior ownerExecuting:
   assumes ! isFMLPSOwnerEmpty(fmlps) && FMLPSMutex_Owner(fmlps) == executing;
   ensures \result == STATUS_UNAVAILABLE;
  behavior waitForOwnership:
   assumes ! isFMLPSOwnerEmpty(fmlps) && FMLPSMutex_Owner(fmlps) != executing && wait;
   ensures \result == STATUS_SUCCESSFUL || \result == STATUS_MUTEX_CEILING_VIOLATED;
  behavior else:
   assumes ! isFMLPSOwnerEmpty(fmlps) && FMLPSMutex_Owner(fmlps) != executing && !wait;
   ensures \result == STATUS_UNAVAILABLE;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Seize(
  FMLPS_Control        *fmlps,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlps) && \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPS_Release(
  FMLPS_Control        *fmlps,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlps) && \valid(executing) && \valid(queue_context);
  requires g_status != 0;
  assigns queue_context->deadlock_callout;
  ensures \result == STATUS_SUCCESSFUL || \result == STATUS_MUTEX_CEILING_VIOLATED;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Wait_for_ownership(
  FMLPS_Control        *fmlps,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  assigns \nothing;
  ensures \result == fmlpsCurrentPriority(fmlps);
*/
RTEMS_INLINE_ROUTINE Priority_Control _FMLPS_Get_priority(
  const FMLPS_Control     *fmlps,
  const Scheduler_Control *scheduler
);
/*@
  requires \valid(thread) && \valid(priority_node) && \valid(queue_context);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPS_Remove_priority(
  Thread_Control       *thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(fmlps) && \valid(executing)&& \valid(queue_context);
  assigns fmlps->Wait_queue.Queue.owner;
  behavior cannotSurrender:
   assumes FMLPSMutex_Owner(fmlps) != executing;
   ensures \result == STATUS_NOT_OWNER;
  behavior noHeads:
   assumes fmlps->Wait_queue.Queue.heads == NULL && FMLPSMutex_Owner(fmlps) == executing;
   ensures \result == RTEMS_SUCCESSFUL;
  behavior headsOwner:
   assumes fmlps->Wait_queue.Queue.heads != NULL && FMLPSMutex_Owner(fmlps) == executing;
   ensures \result == RTEMS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _FMLPS_Surrender(
  FMLPS_Control        *fmlps,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(thread) && \valid(fmlps) && \valid(ceiling_priority);
  assigns \nothing;
 */
RTEMS_INLINE_ROUTINE void _FMLPS_Replace_priority(
  FMLPS_Control  *fmlps,
  Thread_Control *thread,
  Priority_Node  *ceiling_priority
);
//@requires \valid(fmlps) && \valid(queue_context);
RTEMS_INLINE_ROUTINE void _FMLPS_Destroy(
  FMLPS_Control        *fmlps,
  Thread_queue_Context *queue_context
);
/************************************************************/

//LOWER LAYER FUNCTIONS CONSIDERED & ABSTRACTED FOR FMLP-S

/************************************************************/
/*@
  assigns \nothing;  //from schedulerimpl.h
  ensures \result == g_scheduler_index;
 */
RTEMS_INLINE_ROUTINE uint32_t _Scheduler_Get_index(
  const Scheduler_Control *scheduler
);
//@ assigns \nothing;   //from tasksimpl.h FMLPL_get_priority
RTEMS_INLINE_ROUTINE rtems_task_priority _RTEMS_Priority_From_core(
  const Scheduler_Control *scheduler,
  Priority_Control         priority
);
//@ assigns \nothing;  //from threadimpl.h for mpcp
void _Thread_Priority_add(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;  //from threadimpl.h for mpcp
void _Thread_Priority_remove(
  Thread_Control       *the_thread,
  Priority_Node        *priority_node,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;  //from threadimpl.h for mpcp
RTEMS_INLINE_ROUTINE void _Thread_Wait_acquire_default(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);
//@ assigns \nothing;  //from threadimpl.h for mpcp
void _Thread_Priority_replace(
  Thread_Control *the_thread,
  Priority_Node  *victim_node,
  Priority_Node  *replacement_node
);
//@ assigns \nothing;  //from threadimpl.h for mpcp
RTEMS_INLINE_ROUTINE void _Thread_Wait_release_default(
  Thread_Control   *the_thread,
  ISR_lock_Context *lock_context
);
// bypass inline assembler
#define _ISR_lock_ISR_enable(_context) (void) _context;
#define _ISR_lock_ISR_disable(_context) (void) _context;
//@assigns \nothing;
void _Thread_Priority_and_sticky_update(
  Thread_Control *the_thread,
  int             sticky_level_change
);
//@assigns \nothing;
Status_Control _Thread_queue_Enqueue_sticky(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);
//@assigns \nothing;
void _Thread_queue_Surrender_sticky(Thread_queue_Queue *queue,
                                    Thread_queue_Heads *heads,
                                    Thread_Control *previous_owner,
                                    Thread_queue_Context *queue_context,
                                    Thread_queue_Operations const *operations);

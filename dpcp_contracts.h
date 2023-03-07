#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/score/dpcp.h>
#include <rtems/score/scheduler.h>
#include <rtems/score/statesimpl.h>
#include "common_contracts.h"
#include <rtems/rtems/tasksdata.h>

/************************************************/

//      LOGIC FUNCTIONS AND PREDICATES

/************************************************/
/*@
  logic Thread_Control* DPCPMutex_Owner(DPCP_Control *m) =
    m->Wait_queue.Queue.owner;
  logic Priority_Control get_Priority(Priority_Aggregation *a) =
    a->Node.priority;
  logic Per_CPU_Control *get_CPU(DPCP_Control *m) =
    m->cpu;
  predicate dpcp_Empty(DPCP_Control *dpcp) =
  	dpcp->Wait_queue.Queue.owner == NULL;
  logic Priority_Control homeSchedulerPriority =
    get_Priority(&g_homenode->Wait.Priority);
  logic Priority_Control DPCPLocalCeiling(DPCP_Control *m) =
    m->Ceiling_priority.priority;
*/

/************************************************/

//      FUNCTIONS CONSIDERED FOR DPCP

/************************************************/
/*@
  requires \valid(dpcp) && \valid(executing) && \valid(queue_context);
  assigns dpcp->Wait_queue.Queue.owner;
  ensures (homeSchedulerPriority)< DPCPLocalCeiling(dpcp) ==> \result == STATUS_MUTEX_CEILING_VIOLATED;
  ensures (homeSchedulerPriority)>=DPCPLocalCeiling(dpcp)  ==> \result == STATUS_SUCCESSFUL;
 */
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Claim_ownership(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dpcp);
  assigns \nothing;
  ensures \result == DPCPMutex_Owner(dpcp);
*/
RTEMS_INLINE_ROUTINE Thread_Control *_DPCP_Get_owner(
  const DPCP_Control *dpcp
);
/*@
  requires \valid(dpcp); //&& \valid(owner);
  assigns dpcp->Wait_queue.Queue.owner;
  ensures dpcp->Wait_queue.Queue.owner == \old(owner);
  ensures \at(dpcp->Wait_queue.Queue.owner, Post) == \at(owner, Pre);
*/
RTEMS_INLINE_ROUTINE void _DPCP_Set_owner(
  DPCP_Control   *dpcp,
  Thread_Control *owner
);
/*@
  assigns \nothing;
  ensures \result == dpcp->Ceiling_priority.priority;
*/
RTEMS_INLINE_ROUTINE Priority_Control _DPCP_Get_priority(
  const DPCP_Control *dpcp
);
/*@
  requires \valid(dpcp) && \valid(queue_context);
  behavior null:
  	  assumes dpcp_Empty(dpcp);
  	  assigns dpcp->Ceiling_priority.priority;
      ensures dpcp->Ceiling_priority.priority == priority_ceiling;
  behavior not_null:
  	  assumes ! dpcp_Empty(dpcp);
  	  assigns \nothing;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE void _DPCP_Set_priority(
  DPCP_Control         *dpcp,
  Priority_Control      priority_ceiling,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dpcp);
  assigns \nothing;
  behavior null:
  	  assumes dpcp_Empty(dpcp);
  	  ensures \result == STATUS_SUCCESSFUL;

  behavior not_null:
  	  assumes ! dpcp_Empty(dpcp);
  	  ensures \result == STATUS_RESOURCE_IN_USE;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Can_destroy(
  DPCP_Control *dpcp
);
/*@
  assigns \nothing;
  ensures \result == get_CPU(dpcp);
*/
RTEMS_INLINE_ROUTINE Per_CPU_Control *_DPCP_Get_CPU(
  DPCP_Control *dpcp
);
//@ assigns dpcp->cpu;
RTEMS_INLINE_ROUTINE void _DPCP_Set_CPU(
  DPCP_Control         *dpcp,
  Per_CPU_Control      *cpu,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dpcp);
  assigns dpcp->cpu;
  behavior locked:
  	  assumes initially_locked;
  	  ensures \result == STATUS_INVALID_NUMBER;
	  assigns \nothing;
  behavior not_locked:
  	  assumes ! initially_locked;
  	  assigns dpcp->cpu;
  	  ensures \result == STATUS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Initialize(
  DPCP_Control            *dpcp,
  const Scheduler_Control *scheduler,
  Priority_Control         ceiling_priority,
  Thread_Control          *executing,
  bool                     initially_locked
);
/*@
  requires \valid(dpcp) && \valid(executing)&& \valid(queue_context);
  assigns dpcp->Wait_queue.Queue.owner;
  assigns queue_context->thread_state, queue_context->deadlock_callout; //wait for owner
  behavior noOwner:
   assumes DPCPMutex_Owner(dpcp) == NULL;
   ensures (homeSchedulerPriority)< DPCPLocalCeiling(dpcp) ==> \result == STATUS_MUTEX_CEILING_VIOLATED;
   ensures (homeSchedulerPriority)>=DPCPLocalCeiling(dpcp)  ==> \result == STATUS_SUCCESSFUL;
  behavior semaphoreExecuting:
   assumes DPCPMutex_Owner(dpcp) != NULL && DPCPMutex_Owner(dpcp) == executing;
   ensures \result == STATUS_UNAVAILABLE;
  behavior semaphoreWaitForOwnership:
   assumes DPCPMutex_Owner(dpcp) != NULL && DPCPMutex_Owner(dpcp) != executing && wait;
   ensures \result == STATUS_SUCCESSFUL;
  behavior else:
   assumes DPCPMutex_Owner(dpcp) != NULL && DPCPMutex_Owner(dpcp) != executing && !wait;
   ensures \result == STATUS_UNAVAILABLE;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Seize(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dpcp) && \valid(executing)&& \valid(queue_context);
  assigns dpcp->Wait_queue.Queue.owner, dpcp->cpu, g_homenode;
  behavior notOwner:
   assumes DPCPMutex_Owner(dpcp) != executing;
   ensures \result == STATUS_NOT_OWNER;
  behavior surrenderPossible:
   assumes DPCPMutex_Owner(dpcp)!= NULL && DPCPMutex_Owner(dpcp) == executing;
   ensures \result == STATUS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Surrender(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(dpcp) && \valid(executing) &&\valid(queue_context);
  assigns queue_context->thread_state, queue_context->deadlock_callout;
  ensures \result == STATUS_SUCCESSFUL;
  ensures \at(queue_context->thread_state, Post) == STATES_WAITING_FOR_MUTEX;
*/
RTEMS_INLINE_ROUTINE Status_Control _DPCP_Wait_for_ownership(
  DPCP_Control         *dpcp,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Migrate(
  Thread_Control *executing,
  DPCP_Control   *dpcp
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Migrate_Back(
  Thread_Control *executing,
  DPCP_Control   *dpcp
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Acquire_critical(
  DPCP_Control         *dpcp,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Release(
  DPCP_Control         *dpcp,
  Thread_queue_Context *queue_context
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _DPCP_Destroy(
  DPCP_Control         *dpcp,
  Thread_queue_Context *queue_context
);

/************************************************/

// LOWER LAYER FUNCTIONS ABSTRACTED IN DPCP

/************************************************/
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Thread_queue_Destroy(
  Thread_queue_Control *the_thread_queue
);
//@ assigns \nothing;  //initialize
void _Thread_queue_Object_initialize(
  Thread_queue_Control *the_thread_queue
);
//@ assigns \nothing; //surrender
RTEMS_INLINE_ROUTINE Thread_Control *_Thread_queue_First_locked(
  Thread_queue_Control          *the_thread_queue,
  const Thread_queue_Operations *operations
);
//@ assigns \nothing;  //surrender
void _Thread_queue_Extract_critical(
  Thread_queue_Queue            *queue,
  const Thread_queue_Operations *operations,
  Thread_Control                *the_thread,
  Thread_queue_Context          *queue_context
);
//@ assigns \nothing;   //from percpu.h //initialize
static inline Per_CPU_Control *_Per_CPU_Get_by_index( uint32_t index );
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_To(
          Thread_Control  *executing,
          Per_CPU_Control *migration_cpu,
          Priority_Node   *ceiling_priority
        );
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _Scheduler_Migrate_Back(
          Thread_Control  *executing,
          Per_CPU_Control *migration_cpu
        );

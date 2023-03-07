#include <rtems/score/coremutex.h>
#include <rtems/score/basedefs.h>
#include <rtems/score/percpu.h>
#include <rtems/score/status.h>
#include <rtems/score/hdga.h>
#include <rtems/score/scheduler.h>
#include <rtems/score/statesimpl.h>
#include "common_contracts.h"
#include <rtems/rtems/tasksdata.h>

/*@ ghost
   extern Thread_Control *g_thread;
 */
/*@
logic Thread_Control* HDGAMutex_Owner(HDGA_Control *m) =
    m->Wait_queue.Queue.owner;
predicate HDGA_has_valid_ticket(HDGA_Control *m, Thread_Control *e) =
    e->ticket.ticket
    == m->ticket_order[m->current_position];
logic Ticket_Control HDGAGetTicketNumber(Thread_Control *e) =
    e->ticket.ticket;
*/

//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _HDGA_Acquire_critical(
  HDGA_Control         *hdga,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(executing);
  assigns \nothing;
  ensures \result == executing->ticket.ticket;
*/
RTEMS_INLINE_ROUTINE Ticket_Control _HDGA_Get_Ticket_number(
  Thread_Control *executing
);
/*@
  requires \valid(hdga);
  assigns hdga->current_position;
  ensures hdga->current_position == hdga->order_size ==> hdga->current_position == 0; 
*/
RTEMS_INLINE_ROUTINE void _HDGA_Increment_Current_Position(
  HDGA_Control *hdga
);

/*@
  requires \valid(hdga);
  assigns \nothing;
  ensures (_Bool)(executing->ticket.ticket == *(hdga->ticket_order + hdga->current_position)) ==> \result == TRUE;
  ensures (_Bool)(executing->ticket.ticket != *(hdga->ticket_order + hdga->current_position)) ==> \result == FALSE;
*/
RTEMS_INLINE_ROUTINE bool _HDGA_Has_Valid_ticket(
  HDGA_Control   *hdga,
  Thread_Control *executing
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _HDGA_Release(
  HDGA_Control         *hdga,
  Thread_queue_Context *queue_context
);

/*@
  requires \valid(hdga);
  assigns \nothing;
  ensures \result == HDGAMutex_Owner(hdga);
*/
RTEMS_INLINE_ROUTINE Thread_Control *_HDGA_Get_owner(
  const HDGA_Control *hdga
);

/*@
  requires \valid(hdga); //&& \valid(owner);
  assigns hdga->Wait_queue.Queue.owner;
  ensures hdga->Wait_queue.Queue.owner == \old(owner);
  ensures \at(hdga->Wait_queue.Queue.owner, Post) == \at(owner, Pre);
*/
RTEMS_INLINE_ROUTINE void _HDGA_Set_owner(
  HDGA_Control   *hdga,
  Thread_Control *owner
);
/*@
  requires \valid(hdga) && \valid(executing) && \valid(queue_context);
  assigns hdga->Wait_queue.Queue.owner;
  ensures \result == STATUS_SUCCESSFUL;
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Claim_ownership(
  HDGA_Control         *hdga,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(hdga) && \valid(scheduler) && \valid(executing);
  assigns hdga->order_size, hdga->current_position, hdga->ticket_order ;
  ensures initially_locked ==> \result == STATUS_INVALID_NUMBER;
  ensures ! initially_locked && hdga->ticket_order == NULL ==> \result == STATUS_NO_MEMORY;
  ensures ! initially_locked && hdga->ticket_order != NULL ==> \result == STATUS_SUCCESSFUL;
 
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Initialize(
  HDGA_Control            *hdga,
  const Scheduler_Control *scheduler,
  Priority_Control         queue_size,
  Thread_Control          *executing,
  bool                     initially_locked
);
/*@
  requires \valid(hdga) && \valid(executing) && \valid(queue_context) ;
  assigns *queue_context;
  ensures \result == STATUS_SUCCESSFUL;
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Wait_for_ownership(
  HDGA_Control         *hdga,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(hdga) && \valid(executing) && \valid(queue_context) ;
  
  behavior noOwner:
   assumes HDGAMutex_Owner(hdga) == NULL && HDGA_has_valid_ticket(hdga, executing);
   assigns hdga->Wait_queue.Queue.owner;
   ensures \result == STATUS_SUCCESSFUL;
  behavior semaphoreExecuting:
   assumes HDGAMutex_Owner(hdga) == executing;
   ensures \result == STATUS_UNAVAILABLE;
  behavior semaphoreWaitForOwnership:
   assumes HDGAMutex_Owner(hdga) != executing && HDGAMutex_Owner(hdga) != NULL && wait;
   ensures \result == STATUS_SUCCESSFUL;
  behavior else:
   assumes HDGAMutex_Owner(hdga) != executing && HDGAMutex_Owner(hdga) != NULL && !wait;
   ensures \result == STATUS_UNAVAILABLE;

  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Seize(
  HDGA_Control         *hdga,
  Thread_Control       *executing,
  bool                  wait,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(hdga) && \valid(executing)&& \valid(queue_context);
  assigns hdga->Wait_queue.Queue.owner,hdga->current_position;
  behavior notOwner:
   assumes HDGAMutex_Owner(hdga) != executing;
   ensures \result == STATUS_NOT_OWNER;
  behavior surrenderPossible:
   assumes HDGAMutex_Owner(hdga)!= NULL && HDGAMutex_Owner(hdga) == executing;
   ensures \result == STATUS_SUCCESSFUL;
  complete behaviors;
  disjoint behaviors;
 */
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Surrender(
  HDGA_Control         *hdga,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context
);
/*@
  requires \valid(hdga);
  assigns \nothing;
  ensures HDGAMutex_Owner(hdga)!= NULL || g_thread != NULL==> \result == STATUS_RESOURCE_IN_USE;
  ensures HDGAMutex_Owner(hdga)== NULL && g_thread == NULL ==> \result == STATUS_SUCCESSFUL;
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Can_destroy( HDGA_Control *hdga );
// ;
/*@
  requires \valid(hdga) && \valid(executing) && \valid(queue_context) ;
  assigns executing->ticket.ticket, hdga->ticket_order[position], executing->ticket.owner  ;
  ensures \result == STATUS_SUCCESSFUL;
  ensures (HDGAGetTicketNumber(executing) == 0) ==> executing->ticket.owner == executing;
  behavior no_ticket_number:
   assumes HDGAGetTicketNumber(executing) == 0; 
   assigns executing->ticket.ticket, hdga->ticket_order[position], executing->ticket.owner ;
  behavior else:
   assumes executing->ticket.ticket != 0;
   assigns hdga->ticket_order[position];
   ensures hdga->ticket_order[position] == executing->ticket.ticket;
  complete behaviors;
  disjoint behaviors;
*/
RTEMS_INLINE_ROUTINE Status_Control _HDGA_Set_thread(
  HDGA_Control         *hdga,
  Thread_Control       *executing,
  Thread_queue_Context *queue_context,
  int   	        position
);
//@ assigns \nothing;
RTEMS_INLINE_ROUTINE void _HDGA_Destroy(
  HDGA_Control         *hdga,
  Thread_queue_Context *queue_context
);
/*
//@ assigns \nothing;
static void _Thread_queue_Destroy(Thread_queue_Control *the_thread_queue);
//@ assigns \nothing;
void _Thread_queue_Release(Thread_queue_Control *the_thread_queue,
                           Thread_queue_Context *queue_context);
 //@ assigns \nothing;                          
static void _Thread_queue_Acquire_critical(Thread_queue_Control *the_thread_queue,
                                                    Thread_queue_Context *queue_context)     ;    
             
  //@ assigns \nothing;  
 static void _Thread_queue_Context_set_thread_state(Thread_queue_Context *queue_context,
                                                            States_Control thread_state);    
  //@ assigns \nothing;
  static void _Thread_queue_Context_set_deadlock_callout(Thread_queue_Context *queue_context,
                                                                void (*deadlock_callout)
                                                                (Thread_Control *the_thread));
  //@ assigns \nothing;
  void _Thread_queue_Enqueue(Thread_queue_Queue *queue,
                           Thread_queue_Operations const *operations,
                           Thread_Control *the_thread,
                           Thread_queue_Context *queue_context);     
  
 //@ assigns \nothing; 
  static void _Thread_queue_Context_clear_priority_updates(Thread_queue_Context *queue_context);    */  
                     
  //@ assigns \nothing;
  void _Thread_queue_Object_initialize(Thread_queue_Control *the_thread_queue);   
  
   //@ assigns \nothing;                                                   
 void _Workspace_Free(void *block);               
 
 //@ assigns \nothing;                         
void _Thread_queue_Extract_critical(Thread_queue_Queue *queue,
                                    Thread_queue_Operations const *operations,
                                    Thread_Control *the_thread,
                                    Thread_queue_Context *queue_context);  
/*@ assigns \nothing; 
  ensures \result == g_thread;*/
  static Thread_Control *_Thread_queue_First_locked(Thread_queue_Control *the_thread_queue,
                                                           Thread_queue_Operations const *operations);                                                                                                                                                                                             

/*
 * Copyright (c) 2010, Swedish Institute of Computer Science.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 * 3. Neither the name of the Institute nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE INSTITUTE AND CONTRIBUTORS ``AS IS'' AND
 * ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
 * ARE DISCLAIMED.  IN NO EVENT SHALL THE INSTITUTE OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 * LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY
 * OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 *
 * This file is part of the Contiki operating system.
 *
 */

/**
 * \file
 *         The Minimum Rank with Hysteresis Objective Function (MRHOF)
 *
 *         This implementation uses the estimated number of
 *         transmissions (ETX) as the additive routing metric,
 *         and also provides stubs for the energy metric.
 *
 * \author Joakim Eriksson <joakime@sics.se>, Nicolas Tsiftes <nvt@sics.se>
 */

/**
 * \addtogroup uip6
 * @{
 */

#include "net/rpl/rpl-private.h"
#include "net/nbr-table.h"
#include "net/judge.h"
#include "../apps/powertrace/powertrace.h"

#define DEBUG DEBUG_NONE
#include "net/ip/uip-debug.h"

static void reset(rpl_dag_t *);
static void neighbor_link_callback(rpl_parent_t *, int, int);
static rpl_parent_t *best_parent(rpl_parent_t *, rpl_parent_t *);
static rpl_dag_t *best_dag(rpl_dag_t *, rpl_dag_t *);
static rpl_rank_t calculate_rank(rpl_parent_t *, rpl_rank_t);
static void update_metric_container(rpl_instance_t *);

rpl_of_t rpl_mrhof = {
  reset,
  neighbor_link_callback,
  best_parent,
  best_dag,
  calculate_rank,
  update_metric_container,
  1
};

/* Constants for the ETX moving average */
#define ETX_SCALE   100
#define ETX_ALPHA   90

/* Reject parents that have a higher link metric than the following. */
#define MAX_LINK_METRIC			10

/* Reject parents that have a higher path cost than the following. */
#define MAX_PATH_COST			100


/* MIN Hoprankinc*/
#define DEFAULT_RANK_INCREMENT  RPL_MIN_HOPRANKINC
#define MIN_DIFFERENCE (RPL_MIN_HOPRANKINC + RPL_MIN_HOPRANKINC / 2) //384

/*
 * The rank must differ more than 1/PARENT_SWITCH_THRESHOLD_DIV in order
 * to switch preferred parent.
 */
#define PARENT_SWITCH_THRESHOLD_DIV	2
#define per 100L
uint16_t bas_rank;

typedef uint16_t rpl_path_metric_t;
/***************** mrhof + of0 *****************/
static rpl_path_metric_t 
calculate_all_path_metric(rpl_parent_t *p, rpl_parent_t *p1, rpl_path_metric_t *cost1, rpl_path_metric_t *cost2)
{ 
  rpl_path_metric_t etx, hc, min_diff;
  uint32_t ec, total;
  uip_ds6_nbr_t *nbr;
  //printf("DAG_RANK(p->rank, p->dag->instance)=%u\n",DAG_RANK(p->rank, p->dag->instance));
  //printf("DAG_RANK1(p1->rank, p1->dag->instance)=%u\n",DAG_RANK(p1->rank, p1->dag->instance));
  //printf("DAG_RANK1(p2->rank, p2->dag->instance)=%u\n", bas_rank);
  if(bas_rank <= DAG_RANK(p1->rank, p1->dag->instance)){
   *cost1 = 1000;
   *cost2 = 0;
  }else{

  if(p == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
  nbr = rpl_get_nbr(p);

  if(nbr == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
    //printf("1. p->mc.obj.etx=%u, p->mc.obj.energy.energy_est=%lu, he=%u\n", p->mc.obj.etx, p->mc.obj.energy.energy_est, DAG_RANK(p->rank, p->dag->instance));
    etx = 1000L-((p->mc.obj.etx + (uint16_t)nbr->link_metric)*1000L)/65535L;
    ec = 1000L-((p->mc.obj.energy.energy_est) *10L) / 75L;//+ min_diff
    hc = 1000L-(DAG_RANK(p->rank, p->dag->instance)*1000L / topo_num);
    *cost1 = ((uint32_t)etx * E + ec * Po + (uint32_t)hc * R) / per;; // /per
    //printf("1.total1 = %u, etx = %u, ec = %lu, hc = %u\n", *cost1, etx, ec, hc);
  //}else{

    if(p1 == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
  nbr = rpl_get_nbr(p1);

  if(nbr == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
    
    //printf("2. p->mc.obj.etx=%u, p->mc.obj.energy.energy_est=%lu, he=%u,\n", p1->mc.obj.etx, p1->mc.obj.energy.energy_est, DAG_RANK(p1->rank, p1->dag->instance));
    
    etx = 1000L-((p1->mc.obj.etx + (uint16_t)nbr->link_metric)*1000L)/65535L; // + min_diff
    ec = 1000L-((p1->mc.obj.energy.energy_est) * 10L) / 75L;
    hc = 1000L-(DAG_RANK(p1->rank, p1->dag->instance)*1000L / topo_num);//+MIN_DIFFERENCE
    *cost2 = ((uint32_t)etx * E + ec * Po + (uint32_t)hc * R) / per;
    //printf("2.total2 = %u, etx = %u, ec = %lu, hc = %u\n", *cost2, etx, ec, hc);
  //}
  }
}

/***************** mrhof *****************/
static rpl_path_metric_t
calculate_path_metric(rpl_parent_t *p, int count)
{ 
  uip_ds6_nbr_t *nbr;
  if(p == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
  nbr = rpl_get_nbr(p);
  if(nbr == NULL) {
    return MAX_PATH_COST * RPL_DAG_MC_ETX_DIVISOR;
  }
#if RPL_DAG_MC == RPL_DAG_MC_NONE
  {
    return p->rank + (uint16_t)nbr->link_metric;
  }
#elif RPL_DAG_MC == RPL_DAG_MC_ETX
  if(count == 1)
    return p->mc.obj.etx + (uint16_t)nbr->link_metric;
#elif RPL_DAG_MC == RPL_DAG_MC_CUSTOMIZE
  if(count == 1 ){ // ETX
    return p->mc.obj.etx + (uint16_t)nbr->link_metric;
  }else{ //EC
    return energest_get_current_energy_consumption(0) ;
  }
#elif RPL_DAG_MC == RPL_DAG_MC_ENERGY
  if(count == 2)
    return p->mc.obj.energy.energy_est + (uint32_t)nbr->link_metric + energest_get_current_energy_consumption(0);
#else
#error "Unsupported RPL_DAG_MC configured. See rpl.h."
#endif /* RPL_DAG_MC */
}

static void
reset(rpl_dag_t *dag)
{
  printf("RPL: Reset MRHOF + of0\n");
}

/***************** mrhof *****************/
static void
neighbor_link_callback(rpl_parent_t *p, int status, int numtx)
{
  uint16_t recorded_etx = 0;
  uint16_t packet_etx = numtx * RPL_DAG_MC_ETX_DIVISOR;
  uint16_t new_etx;
  uip_ds6_nbr_t *nbr = NULL;

  nbr = rpl_get_nbr(p);
  if(nbr == NULL) {
    /* No neighbor for this parent - something bad has occurred */
    return;
  }

  recorded_etx = nbr->link_metric;

  /* Do not penalize the ETX when collisions or transmission errors occur. */
  if(status == MAC_TX_OK || status == MAC_TX_NOACK) {
    if(status == MAC_TX_NOACK) {
      packet_etx = MAX_LINK_METRIC * RPL_DAG_MC_ETX_DIVISOR;
    }

    if(p->flags & RPL_PARENT_FLAG_LINK_METRIC_VALID) {
      /* We already have a valid link metric, use weighted moving average to update it */
      new_etx = ((uint32_t)recorded_etx * ETX_ALPHA +
                 (uint32_t)packet_etx * (ETX_SCALE - ETX_ALPHA)) / ETX_SCALE;
    } else {
      /* We don't have a valid link metric, set it to the current packet's ETX */
      new_etx = packet_etx;
      /* Set link metric as valid */
      p->flags |= RPL_PARENT_FLAG_LINK_METRIC_VALID;
    }

    PRINTF("RPL: ETX changed from %u to %u (packet ETX = %u)\n",
        (unsigned)(recorded_etx / RPL_DAG_MC_ETX_DIVISOR),
        (unsigned)(new_etx  / RPL_DAG_MC_ETX_DIVISOR),
        (unsigned)(packet_etx / RPL_DAG_MC_ETX_DIVISOR));
    /* update the link metric for this nbr */
    nbr->link_metric = new_etx;
  }
}
/***************** of0 *****************/
static rpl_rank_t
calculate_rank(rpl_parent_t *p, rpl_rank_t base_rank)
{ /*
  rpl_rank_t new_rank;
  rpl_rank_t rank_increase;
  uip_ds6_nbr_t *nbr;

  if(p == NULL || (nbr = rpl_get_nbr(p)) == NULL) {
    if(base_rank == 0) {
      return INFINITE_RANK;
    }
    rank_increase = RPL_INIT_LINK_METRIC * RPL_DAG_MC_ETX_DIVISOR;
  } else {
    rank_increase = nbr->link_metric;
    if(base_rank == 0) {
      base_rank = p->rank;
    }
  }

  if(INFINITE_RANK - base_rank < rank_increase) {
    /* Reached the maximum rank. 
    new_rank = INFINITE_RANK;
  } else {
    /*Calculate the rank based on the new rank information from DIO or
     stored otherwise. 
    printf("base=%d\n",base_rank);
    printf("rank_increase=%d\n",rank_increase);
    new_rank = base_rank + rank_increase;
  }
  printf("rank=%u\n", new_rank);
  return new_rank;
  */
  rpl_rank_t increment;
  if(base_rank == 0) {
    if(p == NULL) {
      return INFINITE_RANK;
    }
    base_rank = p->rank;
  }

  increment = p != NULL ?
                p->dag->instance->min_hoprankinc :
                DEFAULT_RANK_INCREMENT;

  if((rpl_rank_t)(base_rank + increment) < base_rank) {
    printf("RPL: OF0 rank %d incremented to infinite rank due to wrapping\n",
        base_rank);
    return INFINITE_RANK;
  }

  bas_rank = (base_rank + increment)/256;
  //printf("base_rank=%u\n",bas_rank);
  return base_rank + increment;
  
}
/***************** mrhof + of0 *****************/
static rpl_dag_t *
best_dag(rpl_dag_t *d1, rpl_dag_t *d2)
{
  if(d1->grounded != d2->grounded) {
    return d1->grounded ? d1 : d2;
  }

  if(d1->preference != d2->preference) {
    return d1->preference > d2->preference ? d1 : d2;
  }

  return d1->rank < d2->rank ? d1 : d2;
}


static rpl_parent_t *
best_parent(rpl_parent_t *p1, rpl_parent_t *p2)
{
  rpl_dag_t *dag;
  rpl_path_metric_t p1_metric; // p1_metric
  rpl_path_metric_t p2_metric; // p2_metric
  /*uint8_t p1_ip, p2_ip;
  p1_ip = ((uint8_t*)(rpl_get_parent_ipaddr(p1)))[15];
  p2_ip = ((uint8_t*)(rpl_get_parent_ipaddr(p2)))[15];
  printf("p1_ip=%d, p2_ip=%d\n",p1_ip, p2_ip);*/
  
  dag = p1->dag; /* Both parents are in the same DAG. */

  #if RPL_DAG_MC == RPL_DAG_MC_CUSTOMIZE
  //p1_metric = calculate_all_path_metric(p1,1);
  //p2_metric = calculate_all_path_metric(p2,2);
  calculate_all_path_metric(p1, p2, &p1_metric, &p2_metric);
  //printf("******p1_metric = %u\n  ",p1_metric);
  //printf("******p2_metric = %u\n",p2_metric);

  #elif RPL_DAG_MC == RPL_DAG_MC_ETX
  rpl_path_metric_t min_diff;
  min_diff = RPL_DAG_MC_ETX_DIVISOR /
             PARENT_SWITCH_THRESHOLD_DIV; //min = 128
  p1_metric = calculate_path_metric(p1,1);
  p2_metric = calculate_path_metric(p2,1);
  if(p1 == dag->preferred_parent || p2 == dag->preferred_parent) {
    if(p1_metric < p2_metric + min_diff &&
       p1_metric > p2_metric - min_diff) {
      PRINTF("RPL: MRHOF hysteresis: %u <= %u <= %u\n",
             p2_metric - min_diff,
             p1_metric,
             p2_metric + min_diff);
      return dag->preferred_parent;
    }
  }
  #endif
  /* Maintain stability of the preferred parent in case of similar ranks. */
  return p1_metric >= p2_metric ? p1 : p2;
}

#if RPL_DAG_MC == RPL_DAG_MC_NONE
static void
update_metric_container(rpl_instance_t *instance)
{
  instance->mc.type = RPL_DAG_MC;
}
#else
static void
update_metric_container(rpl_instance_t *instance)
{
  rpl_path_metric_t path_metric;
  rpl_dag_t *dag;
#if RPL_DAG_MC == RPL_DAG_MC_ENERGY
  uint8_t type;
#endif

  instance->mc.type = RPL_DAG_MC;
  instance->mc.flags = RPL_DAG_MC_FLAG_P;
  instance->mc.aggr = RPL_DAG_MC_AGGR_ADDITIVE;
  instance->mc.prec = 0;

  dag = instance->current_dag;

  if (!dag->joined) {
    PRINTF("RPL: Cannot update the metric container when not joined\n");
    return;
  }

#if RPL_DAG_MC == RPL_DAG_MC_ETX
  if(dag->rank == ROOT_RANK(instance)) {
    path_metric = 0;
  } else {
    path_metric = calculate_path_metric(dag->preferred_parent, 1);
  }
  instance->mc.length = sizeof(instance->mc.obj.etx);
  instance->mc.obj.etx = path_metric;

  PRINTF("RPL: My path ETX to the root is %u.%u\n",
	instance->mc.obj.etx / RPL_DAG_MC_ETX_DIVISOR,
	(instance->mc.obj.etx % RPL_DAG_MC_ETX_DIVISOR * 100) /
	 RPL_DAG_MC_ETX_DIVISOR);
#elif RPL_DAG_MC == RPL_DAG_MC_CUSTOMIZE
  if(dag->rank == ROOT_RANK(instance)) {
    path_metric = 0;
    instance->mc.length = sizeof(instance->mc.obj.etx);
    instance->mc.obj.etx = path_metric;
    instance->mc.obj.energy.energy_est = path_metric;
  }else{
    instance->mc.length = sizeof(instance->mc.obj.etx);
    instance->mc.obj.etx = calculate_path_metric(dag->preferred_parent, 1);
    instance->mc.obj.energy.energy_est = calculate_path_metric(dag->preferred_parent, 2);
    //printf("instance->mc.obj.etx=%u\n",instance->mc.obj.etx);
    //printf("instance->mc.obj.energy.energy_est=%lu\n", instance->mc.obj.energy.energy_est);
  }
#elif RPL_DAG_MC == RPL_DAG_MC_ENERGY
  if(dag->rank == ROOT_RANK(instance)) {
    path_metric = 0;
  } else {
    path_metric = calculate_path_metric(dag->preferred_parent, 2);
  }

  instance->mc.length = sizeof(instance->mc.obj.energy);

  if(dag->rank == ROOT_RANK(instance)) {
    type = RPL_DAG_MC_ENERGY_TYPE_MAINS;
  } else {
    type = RPL_DAG_MC_ENERGY_TYPE_BATTERY;
  }

  instance->mc.obj.energy.flags = type << RPL_DAG_MC_ENERGY_TYPE;
  instance->mc.obj.energy.energy_est = path_metric;
#endif /* RPL_DAG_MC == RPL_DAG_MC_ETX */
}
#endif /* RPL_DAG_MC == RPL_DAG_MC_NONE */

/** @}*/

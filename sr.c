#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "gbn.h"

/* ******************************************************************
   Selective Repeat protocol.

   Network properties:
   - one way network delay averages five time units (longer if there
   are other messages in the channel for GBN), but can be larger
   - packets can be corrupted (either the header or the data portion)
   or lost, according to user-defined probabilities
   - packets will be delivered in the order in which they were sent
   (although some can be lost).

   Modifications:
   - added SR implementation
**********************************************************************/

#define RTT  16.0       /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6    /* the maximum number of buffered unacked packet */
#define SEQSPACE 12      /* the min sequence space for GBN must be at least windowsize + 1 */
#define NOTINUSE (-1)   /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver  
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your 
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
  int checksum = 0;
  int i;

  checksum = packet.seqnum;
  checksum += packet.acknum;
  for ( i=0; i<20; i++ ) 
    checksum += (int)(packet.payload[i]);

  return checksum;
}

bool IsCorrupted(struct pkt packet)
{
  if (packet.checksum == ComputeChecksum(packet))
    return (false);
  else
    return (true);
}


/********* Sender (A) variables and functions ************/

static struct pkt A_buffer[WINDOWSIZE];  /* array for storing packets waiting for ACK */
static bool A_ackedpkts[SEQSPACE];     /* array for keep track of which packets have been ACKed */
static int A_windowfirst, A_windowlast;    /* array indexes of the first/last packet awaiting ACK */
static int A_windowcount;                /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;               /* the next sequence number to be used by the sender */

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
  struct pkt sendpkt;
  int i;

  /* if not blocked waiting on ACK */
  if ( A_windowcount < WINDOWSIZE) {
    if (TRACE > 1)
      printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

    /* create packet */
    sendpkt.seqnum = A_nextseqnum;
    sendpkt.acknum = NOTINUSE;
    for ( i=0; i<20 ; i++ ) 
      sendpkt.payload[i] = message.data[i];
    sendpkt.checksum = ComputeChecksum(sendpkt); 

    /* put packet in window buffer */
    /* windowlast will always be 0 for alternating bit; but not for GoBackN */
    A_windowlast = (A_windowlast + 1) % WINDOWSIZE; 
    A_buffer[A_windowlast] = sendpkt;
    A_windowcount++;

    /* send out packet */
    if (TRACE > 0)
      printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
    tolayer3 (A, sendpkt);

    /* start timer if first packet in window */
    if (A_windowcount == 1)
      starttimer(A,RTT);

    /* get next sequence number, wrap back to 0 */
    A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;  
  }
  /* if blocked,  window is full */
  else {
    if (TRACE > 0)
      printf("----A: New message arrives, send window is full\n");
    window_full++;
  }
}


/* called from layer 3, when a packet arrives for layer 4 
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{
  /* if received packet is not corrupted */ 
  if (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----A: uncorrupted ACK %d is received\n",packet.acknum);
    total_ACKs_received++;

    /* check if new ACK or duplicate */
    if (A_windowcount != 0) {
      /* variables to track the first and last sequence values in the buffer */
      int seqfirst = A_buffer[A_windowfirst].seqnum;
      int seqlast = A_buffer[A_windowlast].seqnum;

      /* used to determine whether the window has moved */
      int old_windowfirst = A_windowfirst;

      /* check case when seqnum has and hasn't wrapped */
      if (((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
          ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) {

        /* packet is a new ACK */
        if (TRACE > 0)
          printf("----A: ACK %d is not a duplicate\n",packet.acknum);
        new_ACKs++;

        /* individual ACK per packet that is received */
        A_ackedpkts[packet.acknum] = true;

        /* slide window if oldest packet has been ACKed (continue until the program hits an unACKed packet) Also reset ackedpacket array and window count */
        while (A_windowcount > 0 && A_ackedpkts[A_buffer[A_windowfirst].seqnum]) {
            A_ackedpkts[A_buffer[A_windowfirst].seqnum] = false;
            A_windowfirst = (A_windowfirst + 1) % WINDOWSIZE;
            A_windowcount--;
        }

        /* start timer again if there are still more unacked packets in window */
        if (A_windowfirst != old_windowfirst) {
          stoptimer(A);
          if (A_windowcount > 0)
            starttimer(A, RTT);
        }

        /* After all packets have been processed stop the timer */
        if (A_windowcount == 0) {
          stoptimer(A);
        }

      }
    }
    else {
      if (TRACE > 0)
        printf ("----A: duplicate ACK received, do nothing!\n");
    }
  }
  else {
    if (TRACE > 0)
      printf ("----A: corrupted ACK is received, do nothing!\n");
  }
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
  /* As only one timer is available only the oldest unACKed packet is retransmitted */
  if (TRACE > 0)
    printf("----A: time out,resend packets!\n");

  if (TRACE > 0) {
    printf ("---A: resending packet %d\n", (A_buffer[(A_windowfirst) % WINDOWSIZE]).seqnum);
  }

  /* Send oldest unACKed packet only, increase the count and restart timer */
  tolayer3(A,A_buffer[(A_windowfirst) % WINDOWSIZE]);
  packets_resent++;
  starttimer(A,RTT);
}       



/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
  int i;

  /* initialise A's window, buffer, sequence number and ackedpkts array */
  A_nextseqnum = 0;  /* A starts with seq num 0, do not change this */
  A_windowfirst = 0;
  A_windowlast = -1;   /* windowlast is where the last packet sent is stored.  
		     new packets are placed in winlast + 1 
		     so initially this is set to -1
		   */
  A_windowcount = 0;

  for (i = 0; i < SEQSPACE; i++) {
    A_ackedpkts[i] = false;   /* initialises acked packets array with false */
  }
}



/********* Receiver (B)  variables and procedures ************/

static struct pkt B_buffer[WINDOWSIZE];  /* array for storing packets that have been received and ACKed */
static bool B_ackedpkts[SEQSPACE];     /* array for keep track of which ACKs have been buffered vs. received */
static int recvbase;  /* the sequence number expected next by the receiver */
static int B_nextseqnum;   /* the sequence number for the next packets sent by B */

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
  struct pkt sendpkt;
  int i;
  int recvend;
  int inwindow;

  /* if not corrupted */
  if  (!IsCorrupted(packet)) {
    if (TRACE > 0)
      printf("----B: packet %d is correctly received, send ACK!\n",packet.seqnum);
    packets_received++;

    /* Tracks index of the end of the window */
    recvend = (recvbase + WINDOWSIZE) % SEQSPACE;

    /* Checks if the received packet is within the receive window */
    inwindow = (recvbase <= recvend)
        ? (packet.seqnum >= recvbase && packet.seqnum < recvend)
        : (packet.seqnum >= recvbase || packet.seqnum < recvend);


    /* Buffers packets and slides the receiver window */
    if (inwindow) {
      B_buffer[packet.seqnum % WINDOWSIZE] = packet;
      B_ackedpkts[packet.seqnum] = true;

      /* update receive base upon ACK status of oldest packet */
      while (B_ackedpkts[recvbase] == true) {
        /* deliver to receiving application */
        tolayer5(B, B_buffer[recvbase % WINDOWSIZE].payload);
        B_ackedpkts[recvbase] = false;
        recvbase = (recvbase + 1) % SEQSPACE;
      }
    }

    /* create packet (sending back the required seqnum ACK) */
    sendpkt.acknum = packet.seqnum;
    sendpkt.seqnum = B_nextseqnum;
    B_nextseqnum = (B_nextseqnum + 1) % 2;

    /* we don't have any data to send.  fill payload with 0's */
    for ( i=0; i<20 ; i++ ) 
      sendpkt.payload[i] = '0';

    /* computer checksum */
    sendpkt.checksum = ComputeChecksum(sendpkt); 

    /* send out packet */
    tolayer3 (B, sendpkt);
  }
  else {
    /* packet is corrupted */
    if (TRACE == 1) 
      printf("----B: packet corrupted or not expected sequence number, wait for new packet!\n");
  }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
  int i;

  recvbase = 0;   /* Recvbase starts at 0 and tracks the beginning of the receiver's window */
  B_nextseqnum = 1;   /* Holds data for what sequence is expected next which is 1 (after base 0) */

  for (i = 0; i < SEQSPACE; i++) {
    B_ackedpkts[i] = false;   /* Initialises acked packets array to false */
  }
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)  
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}


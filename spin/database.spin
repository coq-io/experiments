/*
DataBase example
*/

/*
After the description in Valmari LNCS 483
*/

#define N 10
#define PID byte

PID holder = N;

bool up[N];
byte ack[N];

proctype P(byte i)
{

   byte j;

   do
   ::  d_step{holder == N /* db is free */ -> 
 
       /* update and send messages */
       holder = i;       
       do
       :: j < N ->  up[j] = true;j++;
       :: else -> j = 0;  break
       od
       };

       /* receive acknowledgments */
       d_step{
          ack[i] == N-1 -> /* all acks received */
         /* release db */ 
          holder = N;
          ack[i] = 0; 
       };

   :: /* else -> */
      
      /* receive message*/ 
      d_step{
        (holder < N) && up[i] ->
        up[i] = false}
      ;
  
      /* send acknowledgment */
      ack[holder]++; 
   od;

  
}


init
{

   atomic{
   byte i;
   do
   :: i < N  -> run P(i); i++;
   :: else -> break
   od;
   }
}

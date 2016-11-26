#!/usr/bin/perl
#
# Compute the K-terminal reliability of a circular arc graph.
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

# globals
$n=10;  # the number of vertices (problem size)
$target_p=0.4;  # the probability that node is a target node 
$p=0.7;  # the failure probability of each node, target node=0, nontarget node=$q

$q=1-$p;
@q=();   

$K=Set::Scalar->new; ; #the set of K target nodes
@a=@b=();
@circular_arc_diagram=();

$run=0;  # denote the number of unreliable runs
$m=0; # the number of unreliable scanlines
@A=(); # minimal separators
@P=(); #the immediate predecessors of (p1, p2) => (p1-1,p2) and (p1,p2-1)
@ps=(); # the partial order set; $ps[$i]: denote the set of scanlines less than scanline i
@f=();

while ( $test++ < 100 ){ # test 100 random instances	
  &new_g();# create a random circular-arc graph
	next if ($K->size < 2); # G must have at least two target vertices
	
	$ktr1=&compute_KTR();	# apply our proposed algorithm
	next if ($ktr1==1);   # KTR=1 when the number of unreliable runs < 2; skip the trivial case
	
	print "\n== test $test: circular-arc diagram: ","@circular_arc_diagram"," ==\n";
	print "target vertices: ",$K,"\n";
	print "our proposed algorithm	 : ";	
	print "KTR=$ktr1\n";
	
	print "the brute-force algorithm: ";
	($ktr2)=&brute_force();
	print "KTR=$ktr2\n";

	if( ($ktr1-$ktr2) > 0.000001 || ($ktr2-$ktr1) > 0.000001 ){
		print "An error occured. Stop!\n";
		exit;
	}
}										 
print "\n Tests completed successfully.\n";


sub compute_KTR {
	&compute_A_P(); # execute Steps 1, 2, 3, and 4 to compute A(k) for each scanpoint k, and immediate predecessors P(s) and partial order set ps(s) for each scanline s	
	return 1 if ($run < 2); # skip if the number of unreliable runs < 2 ==> KTR=1	
	&compute_f(); # execute Step 5 to pre-compute all f(si,sk)	
	return( &compute_R());# execute Step 6 to compute all PrE(s) and R
}

#    arrange the endpoints and scanpoints on the circle circularly as follows:
#    n=10;   ...  (18) 18.5 (19) 19.5 (0) 0.5 (1) 1.5 (2) 2.5 ....
#    the index of scanpoint are from 0 to 2n-1 in the program
sub compute_A_P { 
	my ($i,$j, $s,$k, $v, $z, $start, $run_index, $r, $p1, $p2, $tmp);
	my (@Ap, @Apx, @reliable_scanpoint, @scanline_p1, @scanline_p2, %scanline_p1p2_invert);
  
	@A=();   # A[s]: store the arcs containing the scanline s
	
#-- Step 1: assume that a scanpoint k between every two consecutive endpoints of arcs
	# check whether scanpoint k is a reliable or unreliable
	for ( $s=0.5, $k=0; $s <= 2*$n-0.5 ; $s++, $k++){  # using k as the temporary index of scanpoint (s is the real value)
		$Ap[$k]=Set::Scalar->new;   # store the arcs v containing the unreliable scanpoint k	
		$reliable_scanpoint[$k]=0; # 0: default: mark scanpoint k as a unreliable scanpoint
		for($v=1; $v <= $n ; $v++){
			if (&between($s,$a[$v],$b[$v])){
				if ($K->has($v)){ # v is a reliable arc
					$reliable_scanpoint[$k]=1;# 1: mark scanpoint k as a reliable scanpoint
					$Ap[$k]->insert($v);  # use for checking if G is an interval graph or a disconnected graph					
					last;
				} else {  # v is a unreliable arc
					$Ap[$k]->insert($v);
				}	
			} #if between
		} #for v   
	}
  
# Step 2: split the scanpoints into reliable runs or unreliable runs, and
# Step 3: Starting from the first unreliable scanpoint of an arbitrary unreliable run, label all unreliable scanpoints from 1 to z in the clockwise direction, where z is the number of unreliable scanpoints

  for ($k=0 ; $k < 2*$n; $k++){  # find the first reliable scanpoint k
    last if ($reliable_scanpoint[$k]);
  }
	$start=$k;
  $s=($start+1)%(2*$n); # next scanpoint
  
  $r=0; $z=0;
  @run_index=();  # run_index[z]=r means that the unreliable scanpoint is in run r;
  @Apx=();  # store the arcs containing the scanpoint with new label z
  
  while ( $s!= $start){ # scan circularly
    $s=($s+1)%(2*$n) while ($reliable_scanpoint[$s] && $s!=$start); # reliable_scanpoint -> unreliable scanpoint
    last if ($s==$start);
    for ($j=0; !$reliable_scanpoint[$s] ; $s=($s+1)%(2*$n), $j++){
			$z++;	
			$run_index[$z]=$r;  # the scanpoint z is in unreliable run r;
			$Apx[$z]=Set::Scalar->new;   # store the arcs v containing the scanpoint k
			$Apx[$z]=$Ap[$s]->clone;	  			
    }
    $r++; # run number++
  }
	
	$run=$r;   
	return  if ($run < 2); # if the number of unreliable run < 2 then return
	
# Step 4: compute A(s) and P(s) for each unreliable scanpoint s	
  $k=0; 
  @A=();  
  %scanline_p1p2_invert=(); @scanline_p1=(); @scanline_p2=();
  $s=0;  
  for ($p1=1; $p1 <= $z-1 ; $p1++){
    for ($p2=$z ; $p2 >=$p1+1; $p2--){
	  next if ($run_index[$p1]==$run_index[$p2]); # skip if p1 and p2 are in the same run
	  
			#-- compute A(s): the set of arcs which contains at least one endpoint of unreliable scanline s
			$A[$s]=Set::Scalar->new;  # the set of arcs that contain at least one endpoint (p1 or p2) of unreliabile scanline s
			$A[$s]=$Apx[$p1]+$Apx[$p2]; # union of the arcs containing p1 and p2 which are endpoints of unreliable scanline s

			$scanline_p1[$s]=$p1;  # mark p1 is one endpoint of the scanline s
			$scanline_p2[$s]=$p2;	 # mark p2 is another endpoint of the scanline s	  
			$tmp=$p1."#".$p2;
			$scanline_p1p2_invert{$tmp}=$s;

			#-- compute P(s): the set of all immediate predecessors of unreliable scanline s
			$P[$s]= Set::Scalar->new;	 	 
			$p1x=$p1-1; $p2x=$p2+1;
			if ( defined($scanline_p1p2_invert{"$p1x#$p2"}) ){
				$s1=$scanline_p1p2_invert{"$p1x#$p2"};
				$P[$s]->insert($s1);		 
			}
			if ( defined($scanline_p1p2_invert{"$p1#$p2x"}) ){
				$s2=$scanline_p1p2_invert{"$p1#$p2x"};
				$P[$s]->insert($s2);		 
			}
			$s++;
		} # for p2
	}	# for p1
	
  $m=$s; # m denotes the number of unreliable scanlines
	
  #-- compute the partial order sets
  @ps=();
	for ($i=0; $i < $m ; $i++){
		$ps[$i]= Set::Scalar->new;     
		for ($j=0; $j < $m ; $j++){
			next if ($i==$j);    
			# check if j < i----------->
			if ($scanline_p1[$j] <= $scanline_p1[$i] && $scanline_p2[$j] >= $scanline_p2[$i] ){
				$ps[$i]->insert($j);  # j < i
			}	  
		}
	}
}

# pre-compute all f(si,sk)
sub compute_f {
	my ($k, $kx, $i,$q, $v);
	@f=();
	for ($k=0; $k<$m; $k++){
		foreach $kx ($P[$k]->elements){  # for each immediate predecessor kx of k (at most 2 immediate predecessors for each k)
			$f[$kx][$k]=1;
			foreach $i ($ps[$kx]->elements){
				$f[$i][$k]=$f[$i][$kx]; # the initial value
			}
			$Qv=$A[$kx]-$A[$k];
			foreach  $v ($Qv->elements){		  
				$f[$kx][$k]=$f[$kx][$k]*$q[$v];
				foreach $i ($ps[$kx]->elements){ 
					if ( $A[$i]->has($v)){
						$f[$i][$k]=$f[$i][$k]*$q[$v];
					}
				}
			}
		}
	}
}

# compute Pr[E(sk)] and Rk(A)
sub compute_R {
  my ($k, $i, $R, $qvs, $v);
  my @PrE=();
  
  for ($k=0; $k < $m; $k++){
    $PrE[$k]=1;    
    foreach $i ($ps[$k]->elements){ # for each predecessor of k
        $PrE[$k] -= $PrE[$i]*$f[$i][$k];
    }
  }

  $R=1; 
  for ($k=0; $k < $m; $k++){
		$qvs=1;
		for $v ($A[$k]->elements){
			$qvs *= $q[$v];
		}
		$R -= $PrE[$k]*$qvs;
	}
	return($R);
}

#---------------------------------------------------------------------
sub brute_force {
	my($v, $u, $max, $r, $i, $h, $bits, @bit, $pr);
	my $g= Graph::Undirected->new();
	
	for($v=1; $v <= $n ; $v++){  
		$g->add_vertex($v);
	}
	for($u=1; $u <= $n-1; $u++){
		for($v=$u+1; $v <= $n; $v++){  		
			if ( &between($a[$u],$a[$v],$b[$v]) || &between($b[$u],$a[$v],$b[$v]) ){ #a(u) or b(u) are between a(v) and b(v)
				$g->add_edge($u,$v); # u and v are connected	   				
			}elsif ( &between($a[$v],$a[$u],$b[$u]) || &between($b[$v],$a[$u],$b[$u]) ){ #a(v) or b(v) are between a(u) and b(u)
				$g->add_edge($u,$v); # u and v are connected	   
			}
		}
	}
	
	$max=2**$n-1;
	$r=0;
	foreach $i (0..$max){
		$h = $g->copy_graph;	
		$bits = unpack ( "B*", pack("N",$i) );		
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		$pr=1;
		foreach $v ($h->vertices){			
			if ($bit[$v-1] == 1){# v is working
				$pr=$pr*(1-$q[$v]);
			}else{# v is failed
				$pr=$pr*$q[$v];
				$h->delete_vertex($v);
			}
		}#foreach v
		next if ($pr==0);
		if ($h->same_connected_components($K->elements)){
			$r += $pr;
		}  
	}		
	return $r;
}

# create a random circular-arc graph
sub new_g{
	my($v, $k, $pi, $ab, %p);
	
	@a=@b=();
	%p=();
	
	for ($v=1; $v <=$n ; $v++){
		$p{"$v#a"}=rand(1);
		$p{"$v#b"}=rand(1);
	}
	
	@circular_arc_diagram=();
	$pi=0;# scan endpoints from left to right (from 0 to 2n-1)	
	foreach $k (keys %p){	# re-arrange the positions of endpoints ai and bi for all vi		
		($v, $ab)=split("#",$k); 	
		if ($ab eq "a"){ #left endpoint
			$a[$v]=$pi;		
			@circular_arc_diagram[$pi]=$v."_a";
		}else{ #right endpoint			
			$b[$v]=$pi;
			@circular_arc_diagram[$pi]=$v."_b";			
		}
		
		$pi++;	
	}
	#--- set the target nodes
	$K->clear;
	for($v=1; $v <= $n ; $v++){
		if (rand(1) < $target_p){
			$K->insert($v);
			$q[$v]=0;	 # target node
		}else{
			$q[$v]=$q; # non-target node
		}
	}
}

# For 0<= a!=b!=x <= 2n-1, &between($x,$a,$b) ==>  
# check if point x is btween th arc from endpoint a to endpoint b clockwise
sub between{  
	my($x, $a, $b)=@_;
	if ($a < $b){
		if ($a < $x && $x < $b){
			return(1); #x is between a and b
		} else {
			return(0);
		} 		
	} else { # $a > $b  ; the arc (a,b) are crossing the point between 2n and 1
		if ($x > $a || $x < $b){
			return(1);#x is between a and b
		} else {
			return(0);	 
		}
	}
}

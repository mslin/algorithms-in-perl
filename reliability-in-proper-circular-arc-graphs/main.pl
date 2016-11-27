#!/usr/bin/perl
#
# compute the K-terminal reliability of a proper circular arc graph
# complexity: O(|V|+|E|)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

# globals
$n=9;	# the number of vertices; problem size
$target_p=0.4; # the probability that node is a target node 
$p=0.7;    $q=1-$p;

@p=();   # the reliability of each node, target node=1, nontarget node=$p
$K=Set::Scalar->new; ; #the set of K target nodes
@Kx=(); # for proper circular arc graphs 

@a=@b=();
@adj=();  # matrix
@adj_list=(); # link list
@proper_circular_arc_diagram=();
$g=Graph::Undirected->new();	

while ( $test++ < 100 ){ # test 100 random instances	
	&new_g(); # create a random proper circular-arc graph
	next if ($K->size < 2); # at least two target vertices
	&construct_g(); # convert the proer circular arc diagram to the corresponding proper circular arc graph
	
	$ktr1=compute_KTR();
	print "\n== test $test: proper circular-arc diagram: ","@proper_circular_arc_diagram"," ==\n";
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
	my($k,$v,$i,$j,$s,$t);
	my(@f,@qx);
	#-- partiton into some disjoint interval graphs and compute each reliability
	@qx=();  
	$k=scalar(@Kx);
	for($i=0 ; $i <= $k-1; $i++){  # Kx are sorted array which stores the K vertices
		$s=$Kx[$i];
		$t=$Kx[($i+1)%$k];
		$j=$i+1;
		$Q[$j]=&compute_unreliability_proper_interval($s,$t);	# store value into qx starting from 0, 1, 2, ..
	}
  
	#--- compute the reliability of 2-out-of-k  
	return 1 if ($k < 2);
	@f=();
	for ($j=0 ; $j <= $k ; $j++){
		$f[$j][0]=1 ;  #boundary condition for all j when k=0 
	}
	$f[0][1]=$f[0][2]=0; # boundary condition for all h when j=0
	for ($j=1; $j <= $k ; $j++){  # recursive equations
		$f[$j][1]=$Q[$j]*$f[$j-1][0]+(1-$Q[$j])*$f[$j-1][1]; #  h=1
		$f[$j][2]=$Q[$j]*$f[$j-1][1]+(1-$Q[$j])*$f[$j-1][2]; #  h=2
	} 
	return(1-$f[$k][2]);  # return the reliability
}

# compute the unreliability of the proper interval graph from target s to target t
sub compute_unreliability_proper_interval { 
	my($s,$t)=@_;  
	my(@x,@y,@PrF,$sx,$tx,$i,$v);
	
	#-- check if s and t are connected
	if ($adj[$s][$t]==1){# !!!!!
		return(0);  # return unreliability=1
	}
  
	#-- assume s and t are disconnected belows 
	#-- determine x(r), y(r)  for s <= r < t  (x(r)= alpha(r), y(r)=beta(r))    
	for ($r=$s ; $r!=$t ; $r=($r+1)%$n){
		$x[$r]=$r; $y[$r]=$r; # initial values	
		foreach $rx ( @{$adj_list[$r]} ){  # !!!!!	
			if (&between($rx,$s,$t)){ # s <= rx <= t
				if (&between($rx,$s,$x[$r])){  # s <= rx <= $x[r] <= t
					$x[$r]=$rx;
				}
				if (&between($y[$r],$s,$rx)){  # s <= $y[r] <= rx <= t
					$y[$r]=$rx;
				}
			}
		}
	}
	#-- apply Theorem 3 to compute Pr{F(s, t-1)} ==> refer to the paper of proper interval graph
	@PrF=();  
	$PrF[($s-1)%$n]=0;  # boundary condition
	for ($r=$s ; $r!=$t ; $r=($r+1)%$n){  # for s <= r < t
		$qs=(1-$p[$y[$r]]); #initial value# !!!!!
		for ($rx=($r+1)%$n ; $rx != $y[$r] ; $rx=($rx+1)%$n){
			$qs=$qs*(1-$p[$rx]);
		}
		$PrF[$r]=$PrF[($r-1)%$n]+(1-$PrF[($x[$r]-1)%$n])*$p[$r]*$qs;
	}
	return($PrF[($t-1)%$n]);  
}

#------------------------------------------------------
sub brute_force {
	my($v, $u, $max, $r, $i, $h, $bits, @bit, $pr);	
	$max=2**$n-1;
	$r=0;
	foreach $i (0..$max){
		my $h = $g->copy_graph;
		$bits = unpack ( "B*", pack("N",$i) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		$pr=1;
		foreach $v ($h->vertices){			
			if ($bit[$v] == 1){ # v is working
				$pr=$pr*$p[$v];
			}else{ # v is failed
				$pr=$pr*(1-$p[$v]);
				$h->delete_vertex($v);
			}
		}
		next if ($pr==0);  # some of K target vertices fail    
		if ($h->same_connected_components($K->elements)){
				$r += $pr;
		}  
	}
	return $r;
}

# construct the proper circular-arc graph from its representation
sub construct_g {
	my($u,$v);
	$g = Graph::Undirected->new();	
	for ($v=0; $v<=$n-1; $v++){
		$g->add_vertex($v);
	}
	@adj=();
	@adj_list=();

	for($u=0; $u <= $n-2; $u++){
		for($v=$u+1; $v <= $n-1; $v++){  
			next if ($adj[$u][$v]==1 || $adj[$v][$u]==1);
			if ( &between($a[$u],$a[$v],$b[$v]) || &between($b[$u],$a[$v],$b[$v]) ){ #a(u) or b(u) are between a(v) and b(v)
				$g->add_edge($u,$v); # u and v are connected
				$adj[$u][$v]=$adj[$v][$u]=1;			   
				push @{$adj_list[$u]},$v;
				push @{$adj_list[$v]},$u;	   
				next;
			}  
			if ( &between($a[$v],$a[$u],$b[$u]) || &between($b[$v],$a[$u],$b[$u]) ){ #a(v) or b(v) are between a(u) and b(u)
				$g->add_edge($u,$v); # u and v are connected
				$adj[$u][$v]=$adj[$v][$u]=1;		
				push @{$adj_list[$u]},$v;
				push @{$adj_list[$v]},$u;	   
				next;
			}  
			$adj[$u][$v]=$adj[$v][$u]=0; # u and v are disconnected
		}   
	}
}

# create a random proper circular-arc graph (representation)
sub new_g { 
	my($i,$v,%p,$new_b_n, $new_b_v,@key,$k,$x);
	@a=();
	@b=();

	$a[0]=0; $b[0]=rand(2);      # the interval of v=0 is a real number between 0 and 2

	for ($v=1; $v <=$n-1 ; $v++){# 1<=v<=n-1: a(v)=a(v-1)+rand(b(v-1)-a(v-1)); b(v)=b(v-1)+rand(1);
		$a[$v]=$a[$v-1]+rand($b[$v-1]-$a[$v-1]);
		$b[$v]=$b[$v-1]+rand(1);
	}
  
	#--wrap the proper interval graph to the proper circular arc graph
	if ($b[0] < $a[$n-1]){
		$b[$n-1]=rand($b[0]);  # new_b_n is the new b(n) position
	}else{
		$b[$n-1]=rand($a[$n-1]);  # new_b_n is the new b(n) position
	}

	for ($v=$n-2 ; $v >= 1 ; $v--){
		if ( rand(1) < 0.5 ){# wrap vertex v:  the wrap probability=0.5
			if ($b[$v+1] < $a[$v]){
				$b[$v]=rand($b[$v+1]);  # new_b_n is the new b(n) position
			}else{
				$b[$v]=rand($a[$v]);  # new_b_n is the new b(n) position
			}	  
		}else{ # not wrap
			last;  
		}
	}
  
	#-- relabel the position from integer 0 to 2n
	%p=();
	for ($v=0 ; $v<=$n-1 ; $v++){
		$p{"$v:a"}="$a[$v]";
		$p{"$v:b"}="$b[$v]";
	} # forv 
  
	@key = sort {$p{$a}<=>$p{$b}} keys(%p);

	$i=int(rand(2*$n));  # shuffle !!!!
	#$i=0;               # non-shuffle !!!
	@proper_circular_arc_diagram=();
	foreach $k (@key){
		($v, $x)=split(":",$k);		
		if ($x eq 'a'){	
			$a[$v]=$i;
			@proper_circular_arc_diagram[$i]=$v."_a";			
		}else{	
			$b[$v]=$i;
			@proper_circular_arc_diagram[$i]=$v."_b";						
		}
		$i=($i+1)%(2*$n);
	}
  
  #--- set the target nodes
	$K->clear; @Kx=();
	for($v=0; $v <= $n-1 ; $v++){
		if (rand(1) < $target_p){
			$K->insert($v);
			push(@Kx,$v);  # for proper circular arc graphs
			$p[$v]=1;  # target node
		}else{
			$p[$v]=$p; # non-target node
		}  
	}
}

# For 0<= a!=b!=x <= 2n-1, &between($x,$a,$b) ==>  
# check if point x is btween th arc from endpoint a to endpoint b clockwise
sub between{   # a->x->b are ordered in the clockwise direction (actually, a, x and b can be either points or arcs index
	my($x, $a, $b)=@_;
	if ($a <= $b){
		if ($a <= $x && $x <= $b){
			return(1); #x is between a and b
		}else{
			return(0);
		} 		
	}else{ # $a > $b  ; the arc (a,b) are crossing the point between 2n and 1
		if ($x >= $a || $x <= $b){
			return(1);#x is between a and b
		}else{
			return(0);	 
		}
	}
}

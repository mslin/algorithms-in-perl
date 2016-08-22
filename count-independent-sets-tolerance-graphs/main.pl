#!/usr/bin/perl
#
# Conut independet sets(IS), maximal independent sets(MIS), and independent perfect dominating sets(IPDS) in a tolerance graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=10;# problem size
$u_ratio=0.5; # the probability that a vertex is an unbounded

$U = Set::Scalar->new;     # store unbounded vertices
$B = Set::Scalar->new;     # store bounded vertices

@a=(); # store the left endpoint for each v in the original(interval) representation of tolerance graph 
@b=(); # store the right endpoint for each v in the original(interval) representation of tolerance graph 
@t=(); # store the tolerance for each v 
$nb=0; # number of bounded vertices
@adj=(); # the adjacent matrix 

@torder=(); # store topological order of bounded vertices according to the right endpoints
@allorder=(); # for IPDS; store the 'b' point order of all vertices on the top line

@Nhigh=(); # for IPDS; store |N+[k]| note: including k itselt
@Nlow=();  # for IPDS; store |N-[k]| note: including k itselt
@Nall=();  # for IPDS; store |N[k]|=|N+[k]|+|N-[k]|-1 note: including k itselt

#  the parallelograms representation of a tolerance graph used by IS2 and MIS2
#  bounded vertex,eg:length(b-a)=8,tolerance t=3; let c=a+t and let d=b-t
#                  c*--------*b
#                  /        /
#                 /        /
#               a*--------*d  
#  unbounded vertex,eg:length(b-a)=8,tolerance t>8; let c=b and d=a
#                          / *c
#                       /
#                    /
#               d* /
%pc=();  # position of the left endpoint on the top line (or the endpoint of unbounded vertex on the top line)
%pb=();  # position of the right endpoint on the top line
%pa=();  # position of the left endpoint on the bottom line
%pd=();  # position of the right endpoint on the bottom line(or the endpoint of unbounded vertex on the bottom line)
@v_tag=();  # vertex tag on the top line
@bc_tag=(); # (b or c) tag on the top line
@ub_tag=(); # (unbounded or bounded) tag on the top line
$top_max=0; # the maximum position on the top line 
$bottom_max=0;# the maximum position on the bottom line (note: top_max=$bottom_max after executing parallelograms )

while ( $test++ < 20 ){ # test 20 random instances	  
	&new_g();        #generate a tolerance graph randomly

	&topology_sort_bounded(); # topology sorting for bounded vertices by their b endpoints
	&compute_adj(); # compute the adjacent matrix: adj[u][v]	
	&parallelograms(); # transfer to the parallelograms representation
	&compute_N();    # compute allorder and N+(v) N-(v) for IPDS
	
	print "\n== test$test: tolerance graph: ==\n";		
	&print_tolerance_graph();
	&print_parallelograms_representation();
	print "\n";

	print "our proposed algorithm	 : ";	
	($IS1)=&compute_IS(); 
	($MIS1, $IPDS1)=&compute_MIS(); 
	print "|IS|=$IS1 |MIS|=$MIS1 |IPDS|=$IPDS1\n";

	print "the brute-force algorithm: ";	
	($IS2,$MIS2,$IPDS2)=&brute_force();
	print "|IS|=$IS2 |MIS|=$MIS2 |IPDS|=$IPDS2\n";
	
	if ($IS1!=$IS2 || $MIS1!=$MIS2 || $IPDS1!=$IPDS2){
		print "An error occured. Stop!\n";
		exit;
	}  
}
print "\n Tests completed successfully.\n";


# use the parallelograms representation; scan the pc[v],pb[v] from left to right on the topline and increment the L(u,v)
# overall complexity: O(n^2) 
sub compute_IS {  # note: s(u,v)=L(u,v)+R(v)
	#compute the size of R(k)
	@IS=@nR=();
	foreach $k ($B->elements){      
		$IS[$k]=0; # reset
		$nR[$k]=0; # nR[k] denote the size of R[k]
		foreach $j ($U->elements){
			if ($pc[$k] < $pc[$j] && $pc[$j] < $pb[$k] && !$adj[$k][$j]){
				$nR[$k]++;
			}	   
		}
	}
  
	#incremental IS(v) as 2**|L(u,v)+R(v)| for each u < v
	$IS[0]=1; # initial value
	for ($ii=0; $ii<$nb; $ii++){
		$i=$torder[$ii];	
		$nL=0;  #nL denote the size of L(u,v)
		for ($p=$pb[$i]+1; $p <= $top_max ; $p++){
			$j=$v_tag[$p];
			$bc=$bc_tag[$p];
			$ub=$ub_tag[$p];				
			if ($ub eq 'unbounded' && !$adj[$i][$j]){ #j is unbounded and ij not in E
				$nL++;
			}	
			if ($ub eq 'bounded' && $bc eq 'c' && !$adj[$i][$j]){ # scan to c endpoint of the bounded vertex u and u < v
				$IS[$j] = $IS[$j] + $IS[$i]*2**($nL+$nR[$j]);				
			}	  	
		}		
	}
	return($IS[$n+1]);#return the number of IS in the last dummy bounded vertex
}

# compute MIS and IPDS
# use the parallelograms representation pc[v], pb[v] and increment the L(u,v)
# use the parallelograms representation pa[v], pd[v] for marking the leftmost clique boundary
# overall complexity: O(n^2)  
sub compute_MIS {
	@MIS=();  # MIS  (maximal indpendent st)
	@IPDS=(); # for IPDS (Independent Perfect Dominating Set)    
	@RN_sum=();  # for IDPS part
	$LN_sum=0;   # for IPDS part
	
	# Step 1: Compute F(u) for each u in U
	foreach $u ($U->elements){
		$F[$u] = Set::Scalar->new;  # reset
	}  
	foreach $v ($B->elements){      
		$MIS[$v]=0;
		$IPDS[$v]=0;
		$max_d=-1;  
		$RN_sum[$v]=0;
		foreach $u ($U->elements){
			if ($pc[$v] < $pc[$u] && $pc[$u] < $pb[$v] ){	   
				if ($adj[$v][$u] && $pd[$u] > $max_d){ 		  
					$max_d=$pd[$u]; 
					$max_u=$u;
				}
				# for IPDS
				if (!$adj[$v][$u]){
					$RN_sum[$v] += $Nall[$u];	   
				}				
			}
		}
		if ($max_d >= 0){
			$F[$max_u]->insert($v); 
		}
	}
  
	# Step 2: Compute MIS(Gk) for each k in B
	$MIS[0]=1; # initial value
	$IPDS[0]=1; # for IPDS
	for ($ii=0; $ii<$nb; $ii++){
		@mark=(); 
		$i=$torder[$ii];	
		$min_d=$bottom_max+1;
		$LN_sum=0;  # for IPDS
		for ($p=$pb[$i]+1; $p <= $top_max ; $p++){
			$k=$v_tag[$p];
			$bc=$bc_tag[$p];
			$ub=$ub_tag[$p];
			# case 1:
			if ($ub eq 'bounded' && $bc eq 'c' && !$adj[$i][$k]){
				if ($pa[$k] < $min_d) {
					$MIS[$k] = $MIS[$k] + $MIS[$i];
					# for IPDS
					if ( $Nhigh[$i]+$Nlow[$k]+$RN_sum[$k]+$LN_sum == $allorder[$k]-$allorder[$i]+1 ){
						$IPDS[$k] = $IPDS[$k] + $IPDS[$i];
					}		
				}						
			}	 
			# case 2:
			if ($ub eq 'unbounded' && $bc eq 'c' && !$adj[$i][$k]){
				if ($pd[$k] < $min_d){
					$min_d=$bottom_max+1;
				}
				foreach $w ($F[$k]->elements){ # reset mark
					$mark[$w]=1;
				}
				# for IPDS
				$LN_sum += $Nall[$k];								
			}	
			# case 3:
			if ($ub eq 'bounded' && $bc eq 'b' && !$adj[$i][$k]){
				if ($pd[$k] < $min_d && !$mark[$k]){
					$min_d=$pd[$k];
				}	
			}
			
		}
	}
	return($MIS[$n+1], $IPDS[$n+1]);
}

#compute the adjacent matrix
sub compute_adj {
  @adj=();
	for ($u=0 ; $u <= $n ; $u++){
		for ($v=$u+1 ; $v <= $n+1; $v++){
			next if ($u==$v);
			$maxa= $a[$v]>$a[$u] ? $a[$v] : $a[$u];
			$minb= $b[$v]<$b[$u] ? $b[$v] : $b[$u];
			$mint= $t[$v]<$t[$u] ? $t[$v] : $t[$u];
			if ( ($minb-$maxa) >= $mint ){
				$adj[$u][$v]=$adj[$v][$u]=1;		
			}else{
				$adj[$u][$v]=$adj[$v][$u]=0;		 	  
			}
		}
	}
}

# compute allorder and N+(v) N-(v) for IPDS
sub compute_N { # compute N+[] ; N-[]; Nall[];
	@allorder=();
	for ($i=0, $j=0; $i <= $top_max ; $i++){ # scan the top line from 0 to top_max
		$v=$v_tag[$i];
		$bc=$bc_tag[$i];
		$ub=$ub_tag[$i];	  	  
		if ($bc eq 'b' || ( $bc eq 'c' && $ub eq 'unbounded')){ # bounded b point or unbounded c point	    
			$allorder[$v]=$j++;
		}  
	}  
	@Nhigh=@Nlow=@Nall=();  
	for($i=0; $i <= $n+1; $i++){ 
		$Nall[$i]=$Nhigh[$i]=$Nlow[$i]=1;  # include i itself
		for ($j=0 ; $j <= $n+1; $j++){
			if ($adj[$i][$j] && $i!=$j){ # i and j are adjacent
				$Nall[$i]++; 
				if ($allorder[$i] < $allorder[$j]){ # i,j could be U or B
					$Nhigh[$i]++;             
				}else{
					$Nlow[$i]++;
				}
			}
		} 
	}
}

#produce the topological order according to b values
sub topology_sort_bounded {
	@torder=();    
	@torder= (sort {$b[$a]<=>$b[$b]} $B->elements); # sort by b values	
}

# construct a random tolerance graph
sub new_g { 
	@a=@b=@t=();
	$U=Set::Scalar->new;  # clear U set
	$B=Set::Scalar->new;  # clear B set

	$v=1;
	while ($v <= $n ){ 
		$a[$v]=rand(2*$n)+1;  # real number between 1~2n
		$b[$v]=rand(2*$n)+1;  # real number between 1~2n
		if ($a[$v] > $b[$v]){# swap
			$tmp=$a[$v];
			$a[$v]=$b[$v];
			$b[$v]=$tmp;
		}
		$v++ if (($b[$v]-$a[$v]) >= 1 ); # ok, try next vertex
	} 

	#setup tolerance
	for ($v=1; $v <= $n ; $v++){
		$len=$b[$v]-$a[$v];
		if ( rand(1) < $u_ratio ){ #unbounded vertex	   
			$t[$v]=$len+1; # unbounded tolerance 	   
			$U->insert($v);
		}else{ #bound vertex	   
			$t[$v]=$len*rand(1);  # bounded tolerance
			$B->insert($v);
		}
	}
	
	# Add two dummy bounded vertices 0 and n+1 with tolerance 0
	$a[$n+1]=2*$n+1; $b[$n+1]=2*$n+2;
	$a[0]=0; $b[0]=1;
	$t[0]=$t[$n+1]=0.5;
	$B->insert(0);
	$B->insert($n+1);
	$nb=$B->size;  # nb denote the number of bounded vertices	
}


#convert to parallelograms representation
sub parallelograms {
 #  bounded vertex,eg:(len=8, toleranc=3)
 #                  c*--------*b
 #                  /        /
 #                 /        /
 #               a*--------*d  
 #  unbounded vertex,eg:(len=8)
 #                          / *c
 #                       /
 #                    /
 #               d* /
	
	%p=();   # reset;
	@pc=();  # reset; the position of left endpoint on the top line
	@pb=();  # reset; the position of right endpoint on the top line
	@pa=();  # reset; the position of left endpoint on the bottom line
	@pd=();  # reset; the position of right endpoint on the bottom line
	%c=();   # reset;
	@v_tag=(); # rest ;  vertex tag on the top line
	@bc_tag=(); # reset; (b or c) tag on the top line
	@ub_tag=(); # reset; (unbounded or bounded) tag on the top line
 
	@v_tag2=(); # reset;  tag on the bottom line
	@ad_tag2=(); # reset; (a or d)  tag on the bottom line
	@ub_tag2=(); # reset;  (unbounded or bounded)tag on the bottom line

	# construct the top line
	for ($v=0; $v <= $n+1 ; $v++){
		if ($b[$v] >= $a[$v]+$t[$v]){ # bounded vertex
			$c[$v]=$a[$v]+$t[$v];  #construct c on top line
			$p{"$v:c:bounded:top"}=$c[$v];
			$p{"$v:b:bounded:top"}=$b[$v];
		}else{  # unbounded vertex
			$c[$v]=$b[$v]; #construct c on top line
			$p{"$v:c:unbounded:top"}=$c[$v];
		}	
	}
	
	@key = (sort sortbybvalue keys %p );
	# assign the new position according to the order on top line
	$i=0;
	foreach $k (@key){
		($v, $x, $y, $z)=split(":",$k);
		if ($y eq 'bounded'){ # bounded vertex
			if ($x eq 'c'){
				$pc[$v]=$i;
				$v_tag[$i]=$v;
				$bc_tag[$i]='c';
				$ub_tag[$i]='bounded';
			}else{  # $x == 'b'
				$pb[$v]=$i;  
				$v_tag[$i]=$v;
				$bc_tag[$i]='b';
				$ub_tag[$i]='bounded';
			}	  
		} else { # unbounded vertex
			$pb[$v]=$pc[$v]=$i;
			$v_tag[$i]=$v;
			$bc_tag[$i]='c';
			$ub_tag[$i]='unbounded';	  
		}
		$i++;
	}
	$top_max=$i;
  
	# construct the bottom line
	%p=();# reset
	for ($v=0; $v <= $n+1 ; $v++){
		if ($b[$v] >= $a[$v]+$t[$v]){ # bounded vertex
			$d[$v]=$b[$v]-$t[$v];
			$p{"$v:a:bounded:bottom"}=$a[$v];
			$p{"$v:d:bounded:bottom"}=$d[$v];
		}else{  # unbounded vertex
			$d[$v]=$a[$v];
			$p{"$v:d:unbounded:bottom"}=$d[$v];
		}	
	}

	@key = (sort sortbybvalue keys %p );
	$i=0;
	foreach $k (@key){
		($v, $x, $y, $z)=split(":",$k);
		if ($y eq 'bounded'){ # bounded vertex
			if ($x eq 'a'){# $x == 'a'
				$pa[$v]=$i;
				$v_tag2[$i]=$v;
				$ad_tag2[$i]='a';
				$ub_tag2[$i]='bounded';
			} else {# $x == 'd'
				$pd[$v]=$i;  
				$v_tag2[$i]=$v;
				$ad_tag2[$i]='d';
				$ub_tag2[$i]='bounded';
			}	  
		} else { # unbounded vertex
			$pa[$v]=$pd[$v]=$i;
			$v_tag2[$i]=$v;
			$ad_tag2[$i]='d';
			$ub_tag2[$i]='unbounded';	  
		}
		$i++;
	}
	$bottom_max=$i;  
}

sub brute_force{
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);
	for ($v=1; $v<=$n-1; $v++){
		for ($u=$v+1; $u<=$n; $u++){      
			if ($adj[$v][$u]){
				$g->add_edges([$v,$u]);
			}
		}
	}

	$max=2**$g->vertices-1;
	@vc_set=();
	@vc_set = map { Set::Scalar->new() } 0..$max;

	#for checking independent perfect dominating sets
	my $all_v= Set::Scalar->new(1..$n); # all vertices
	my $mis;  # maximal independet sets
	my $ipds_flag;
	my $nipds=0;

	$nvc=0;
	@min_vc_tag=();
	%hsize=();
	foreach $num (0..$max){
		$bits = unpack ( "B*", pack("N",$num) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);
		%cover=();
		foreach $vs ($g->vertices){
			if ($bit[$vs-1] == 1){
				@edges=$g->edges_at($vs);
				foreach $a (@edges){
					$edge=$$a[0].'-'.$$a[1];
					$cover{$edge}=1;
				}  
				$vc_set[$num]->insert($vs);
			}
		}
		@cover_edge=keys %cover;      
		$vc=$vc_set[$num];
		if ( scalar(@cover_edge) == scalar($g->edges) ){
			$nvc++;       
			$flag=1;
			foreach $i (0..$num-1){
				if ($min_vc_tag[$i]==1){
					$mvi=$vc_set[$i];
					if ( $vc->is_proper_subset($mvi) ){
						$min_vc_tag[$i]=0;
						$flag=1;
					}elsif ( $vc->is_proper_superset($mvi) ){
						$flag=0;
						break;
					}
				}
			}
			if ($flag==1){
				$min_vc_tag[$num]=1;				
				#check independent perfect dominating sets
				$mis=$all_v-$vc; # set difference
				$ipds_flag=1;
				for my $u ($vc->elements) { # u is not in mis
					$dominated=0;
					for my $i ($mis->elements) { # i is in mis
						if ($adj[$i][$u]){                     # u and i are adjacent
							$dominated++; # i dominates u
						}
					}
					if ($dominated != 1){# u is dominated by more than one vertex
						$ipds_flag=0;
						break;
					}
				}
				if ($ipds_flag == 1){  # $mis is a independent perfect dominating sets
					$nipds++;
				}        
			}
		}
	}
	$nmvc=0;
	for ($i=0; $i <= $max ; $i++){
		if ($min_vc_tag[$i]==1){
			$nmvc++;
		}	
	}	
	return($nvc,$nmvc,$nipds); # note: |VC|=|IS| and |MVC|=|MIS|
}

sub sortbybvalue {
	return(-1) if ($p{$a} < $p{$b});
	return(1) if ($p{$a} > $p{$b}); 
}

sub print_tolerance_graph {
	print "interval v[a, b]:\n";
	for ($v=1 ; $v<=$n ; $v++){
		printf(" %d[%3.1f,%3.1f]",$v,$a[$v],$b[$v]);
	}	
	print "\ntolerance v(t): \n";
	for ($v=1 ; $v<=$n ; $v++){
		if ($B->has($v)){ #bounded
			printf(" %d(%4.2f)",$v,$t[$v]);
		}else{ #unbounded
		  print " $v(*)";
		}		
	}
	print "\n";
}

sub print_parallelograms_representation {
	print "parallelograms representation (*: unbounded vertex):\n";
	for ($i=2; $i < $top_max-2 ; $i++){ # skip two dummy vertices
		print " $v_tag[$i]";
		print "*" if ($ub_tag[$i] eq "unbounded");		
	}	
	print "\n";
	for ($i=2; $i < $bottom_max-2 ; $i++){# skip two dummy vertices
		print " $v_tag2[$i]";
		print "*" if ($ub_tag2[$i] eq "unbounded");		
	}		
	print "\n";
}

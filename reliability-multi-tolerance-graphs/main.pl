#!/usr/bin/perl
#
# Compute the 2-terminal reliability of a multi-tolerance graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=9; # the number of vertices (problem size)
$u_ratio=0.5; # the probability that a vertex is an unbounded
$p=0.7;    $q=1-$p;

@p=();   # the reliability of each vertex, target vertex=1, nontarget vertex=$p
$U = Set::Scalar->new;     # store unbounded vertices
$B = Set::Scalar->new;     # store bounded vertices
@v_ub_tag=();     # store the tags (bounded or unbounded) of vertices
@a=(); # store the left endpoint for each v in the original(interval) representation of tolerance graph 
@b=(); # store the right endpoint for each v in the original(interval) representation of tolerance graph 
@lt=(); # store the left tolerance for each v 
@rt=(); # store the right tolerance for each v 
@adj=(); # the adjacent matrix; $adj[$u][$v]=1 if v and u are adjacent
@k_set=();  # store the k target vertices for bounded multitolerance graph (In general, k_set=(source,terminal))

# for the normalized trapezoid representation of a multitolerance graph
#  bounded vertex,eg:length(b-a)=8,left tolerance lt=3 , right tolerance rt=6; let c=a+lt and let d=b-rt
#                  c*------------*b
#                  /            /
#                 /          /
#               a*--------*d  
#  unbounded vertex,eg:length(b-a)=8,tolerance t>8; let c=b and d=a
#                          / *c
#                       /
#                    /
#               d* /
@pb=();  # position of the right endpoint on the top line
@pa=();  # position of the left endpoint on the bottom line
@pd=();  # position of the right endpoint on the bottom line(or the endpoint of unbounded vertex on the bottom line)
@v_tag=();  # vertex tag on the top line
@v_tag2=();  # vertex tag on the bottom line
@bc_tag=(); # (b or c) tag on the top line
@ad_tag2=();# (a or d) tag on the bottom line
@ub_tag=(); # (unbounded or bounded) tag on the top line
@ub_tag2=(); # (unbounded or bounded) tag on the bottom line
$all_max=0;# the maximum position on top and bottom lines

#for computing 2-terminal reliability
@V=(); # minimal cut-sets (separators)
$m=0; # the number of scanlines
@ps=(); # the partial order set; $ps[$i]: denote the set of minimal cut-sets less than cut-set i
@ips=(); #the immediate predecessors of (s1, s2) => (s1-1,s2) and (s1,s2-1)
@f=();
$b_min=$t_min=$b_max=$t_max=0;

while ( $test++ < 20 ){ # test 20 random instances	
	&new_g(); # create a random multi-tolerance graph
	&construct_g();   #convert the interval diagram to the corresponding multi-tolerance graph g
	if ( ! $g->is_connected ){  # assume that the multitolerance graph is connected     
		next;
	}
	print "\n== test$test: multi-tolerance graph: ==\n";	
	&print_multitolerance_graph();  		
	print "bounded vertices  =",$B,"\n";
	print "unbounded vertices=",$U,"\n";
	print "source=$source --> terminal=$terminal\n";
	
	&normalized_trapezoid_representation(); # transfer to the normalized trapezoid representation
	&print_normalized_trapezoid_representation();
	print "\n";
	
	print "our proposed algorithm	 : ";	
	$rel1=&Compute_2TR();
	print "2TR=$rel1\n";
	
	print "the brute-force algorithm: ";
	$rel2=&brute_force();
	print "2TR=$rel2\n";
	
	if (($rel1 - $rel2) > 0.000001 || ($rel2 - $rel1)> 0.000001){
		print "An error occured. Stop!\n";
		exit;
	}  
}
print "\n Tests completed successfully.\n";

sub Compute_2TR {	
  &Compute_V_P(); # compute V(s), ps(s), and ips(s) for each scanline s
  &Compute_f(); # pre-compute all f(si,sk)
	return( &Compute_R());
}

#compute V(s), ps(s), ips(s) for each scanline s
sub Compute_V_P {    
	$k=0; @V=(); %V_map_invert=(); @V_map_b=@V_map_t=(); 
	#-- set the neighbors of source as the first V[0]
	$V[0]=Set::Scalar->new; 	
	$V_map_b[0]=0;
	$V_map_t[0]=0;
	for ($v=1; $v <= $n ; $v++){
		next if ($v==$source);
		if ( $adj[$source][$v] ){  #$v is the neighbor of source
			$V[0]->insert($v);
		}
	}
	
	# setup boundary
	$t_min=$pb[$source]+0.5; 
	$b_min=$pd[$source]+0.5;
	$t_max=$pc[$terminal]-0.5;
	$b_max=$pa[$terminal]-0.5; 
	
	$k=1;
	for ($b=$b_min; $b <= $b_max ; $b++){
		for ($t=$t_min; $t <= $t_max ; $t++){
			$V[$k]=Set::Scalar->new; 			
			$V_map_b[$k]=$b;	 
			$V_map_t[$k]=$t;  	 
			$V_map_invert{"$b#$t"}=$k;
			for($v=1; $v <= $n ; $v++){
				next if ($pd[$v] < $pa[$source] && $pb[$v] < $pc[$source] );  # skip the vertices on the leftside of the (unbounded)soruce vertex
				next if ($pa[$v] > $pd[$terminal] && $pc[$v] > $pb[$terminal] );# skip the vertices on the rightside of the (unbounded)terminal vertex	   
				if ($v_ub_tag[$v] eq 'bounded'){ # v is bounded
					$V[$k]->insert($v) if (!(($pb[$v] < $t && $pd[$v] < $b) || ($pc[$v] > $t && $pa[$v] > $b)));
				} else { # v is unbounded
					$V[$k]->insert($v) if ( $pc[$v] > $t && $pd[$v] < $b );
				}	   
			}
			$k++; 
		}
	}

	#-- set the neighbors of terminal as the last scanline
	$V[$k]=Set::Scalar->new; 
	$V_mini_flag[$k]=1; # initial value	 
	$V_map_b[$k]=2*$n+1;
	$V_map_t[$k]=2*$n+1;
	for ($v=1; $v <= $n ; $v++){
		next if ($v==$terminal);
		if ( $adj[$terminal][$v] ){  #$v is the neighbor of terminal
			$V[$k]->insert($v);
		}
	}

	$k++;
	$m=$k; # m denote the number of scanlines
	
	#compute the partial order sets, ps
	@ps=();
	for ($i=0; $i < $m ; $i++){
		$ps[$i]= Set::Scalar->new;     
		for ($j=0; $j < $m ; $j++){
			next if ($i==$j);
			if (($V_map_b[$j] <= $V_map_b[$i]) && ($V_map_t[$j] <= $V_map_t[$i])){    
				$ps[$i]->insert($j);
			}
		}
	}
	
	#compute the immediate predecessors of ips((b,t)) => {(b-1,t),(b,t-1)}
	@ips=();
	for ($b=$b_min; $b <= $b_max ; $b++){   
		for ($t=$t_min; $t <= $t_max ; $t++){
			$k=$V_map_invert{"$b#$t"};
			$ips[$k]= Set::Scalar->new;	 	 
			$bx=$b-1; $tx=$t-1;
			if ( defined($V_map_invert{"$bx#$t"}) ){
				$k1=$V_map_invert{"$bx#$t"};
				$ips[$k]->insert($k1);		 
			}
			if ( defined($V_map_invert{"$b#$tx"}) ){
				$k2=$V_map_invert{"$b#$tx"};
				$ips[$k]->insert($k2);
			}			
		}
		
	}

	# set the boundary conditions 
	$ips[0]= Set::Scalar->new;# the ips of first one V (N(source)) is an empty set
	$ips[$m-1]= Set::Scalar->new;# the ips of last one scanline (N(terminal)) is the V_map=(b_max, t_max)
	$ips[$m-1]->insert($m-2);
	$ips[1]->insert(0); # the ips of the second scanline (V_map=(b_min,t_min)) is the first one scanline; note: the second scanline may be equal to the last scanline (N(terminal))	
}

# pre-compute all f(si,sk)
sub Compute_f {
	@f=();
	for ($k=0; $k<$m; $k++){
		for $ips ($ips[$k]->elements){  # for each immediate predecessor of k (at most 2 immediate predecessors for each k)
			$f[$ips][$k]=1; # f[ips][k]=pr(V[ips]-V[k]); ips is the immediate predecessor of k		
			for $i ($ps[$ips]->elements){ # for each predecessor of ips
				$f[$i][$k]=$f[$i][$ips];     
			}			
			for $v (($V[$ips]-$V[$k])->elements){
				$q=1-$p[$v];
				$f[$ips][$k]=$f[$ips][$k]*$q;  # prx[ips][k]=pr(V[ips]-V[k]); ips is the immediate predecessor of k          
				for $i ($ps[$ips]->elements){ # for each predecessor of ips
					$f[$i][$k]=$f[$i][$k]*$q if ( $V[$i]->has($v));
				}
			}
		}
	}
}

# compute Pr[E(sk)] and Rx,y(G) //
sub Compute_R {
	# compute PrE
	@PrE=();
	for ($k=0; $k < $m; $k++){
		$PrE[$k]=1;    
		for $i ($ps[$k]->elements){ # for each predecessor of k
			$PrE[$k] -= $PrE[$i]*$f[$i][$k];
		}
	}
	
	# computer reliability
	$R=1;    
	for ($k=0; $k < $m; $k++){
		$tmp=1;
		for $v ($V[$k]->elements){
			$tmp *= (1-$p[$v]);
		}
		$R -= $PrE[$k]*$tmp;	
	}
	return($R);  # return the reliability
}

sub brute_force {
	$max=2**$n-1;
	$r=0;
	foreach $i (0..$max){
		$h = $g->copy_graph;
		$bits = unpack ( "B*", pack("N",$i) );
		@bit=();
		@bit =split(//,$bits);
		@bit = reverse(@bit);  
		$pr=1;
		foreach $v ($h->vertices){
			$px=$p[$v];
			if ($bit[$v-1] == 1){ # v works
				$pr=$pr*$px;
			}else{ # v fails
				$pr=$pr*(1-$px);
				$h->delete_vertex($v);
			}
		}  
		next if ($pr==0);  # some of K target vertices fail    
		if ($h->same_connected_components(@k_set)){
			$r += $pr;
		}  
	}
	return $r;
}


# convert a multi-tolerance diagram to the corresponding multi-tolerance graph g
sub construct_g {
	$g = Graph::Undirected->new();
	for($v=1; $v <= $n ; $v++){  
		$g->add_vertex($v);
	}
	
# check edge connection (using the definition of multitolerance)
# notation in definition: e.g. lv-------ltv-------rtv----rv  or lv----rtv-----ltv--rv
# note: lv=$a[$v]; rv=$b[$v]; ltv=$a[$v]+$lt[$v](=$c[$v]); rtv=$b[$v]-$rt[$v](=$d[$v]);
# definition: tv(x)=[ltv(x), rtv(x)]==> ltv(x)=lv+(rtv-lv)*x; rtv(x)=ltv+(rv-ltv)*x  ;  0<=x<=1
#                x =>the lambda in the definition
	@adj=();
	for($u=1; $u <= $n; $u++){
		for($v=1; $v <= $n; $v++){   
			next if ($u==$v || $adj[$u][$v]==1);
			#   case 1: a(v)--------------b(v) 
			#                   a(u)-----
			if ($a[$v] < $a[$u] && $a[$u] < $b[$v]){ # case 1
				#-- case 1.1: check if there exists tv(x)=[ltv(x),rtv(x)] in [lu, ru] 
				$x= ($a[$u]-$a[$v])/($b[$v]-$rt[$v]-$a[$v]);#let ltv(x)=lu => x=(lu-lv)/(rtv-lv)
				if ($x >=0 && $x <=1){
					$rtvx=$a[$v]+$lt[$v]+($b[$v]-$a[$v]-$lt[$v])*$x;
					if ($rtvx <= $b[$u]){
						$adj[$u][$v]=1;
						$adj[$v][$u]=1;
						$g->add_edge($u,$v); # u and v are connected		 		  
						next;
					}
				}
				#-- case 1.2: check if there exists tu(x)=[ltu(x),rtu(x)] in [lv, rv] 
				if (($a[$u]+$lt[$u]) <= $b[$v]){#just check the case of x=0 ==> tu(0)=[lu, ltu]
					$adj[$u][$v]=1;
					$adj[$v][$u]=1;
					$g->add_edge($u,$v); # u and v are connected		 		  
					next;
				}
			}	   
			#   case 2: a(v)--------------b(v) 
			#                   ----b(u)	   
			if ($a[$v] < $b[$u] && $b[$u] < $b[$v]){
				#-- case 2.1: check if there exists tv(x)=[ltv(x),rtv(x)] in [lu, ru] 	   
				$x= ($b[$u]-$a[$v]-$lt[$v])/($b[$v]-$a[$v]-$lt[$v]);#let rtv(x)=ru => x=(ru-ltv)/(rv-ltv)
				if ($x >=0 && $x <=1){
					$ltvx=$a[$v]+($b[$v]-$rt[$v]-$a[$v])*$x;
					if ($ltvx >= $a[$u]){
						$adj[$u][$v]=1;
						$adj[$v][$u]=1;
						$g->add_edge($u,$v); # u and v are connected		 		  
						next;
					}
				}
				#-- case 2.2: check if there exists tu(x)=[ltu(x),rtu(x)] in [lv, rv] 
				if (($b[$u]-$rt[$u]) >= $a[$v]){ #just check the case of x=1 ==> tu(1)=[rtu, ru]
					$adj[$u][$v]=1;
					$adj[$v][$u]=1;
					$g->add_edge($u,$v); # u and v are connected
					next;
				}
			}
		}
	}
}

#construct a random multitolerance diagram
sub new_g { 
	@a=@b=@lt=@rt=();
	$U=Set::Scalar->new;  # clear U set
	$B=Set::Scalar->new;  # clear B set

	$v=1;
	while ($v <= $n ){ 
		$a[$v]=rand(2*$n);  # real number between 0~2n
		$b[$v]=rand(2*$n);  # real number between 0~2n
		if ($a[$v] > $b[$v]){# swap
			$tmp=$a[$v];
			$a[$v]=$b[$v];
			$b[$v]=$tmp;
		}
		$v++ if (($b[$v]-$a[$v]) >= 1 ); # ok, try next vertex
	} 
	
	#setup tolerance 
	%v_ub_tag=();
	for ($v=1; $v <= $n ; $v++){
		$len=$b[$v]-$a[$v];
		if ( rand(1) < $u_ratio ){ #unbounded vertex	   
			$lt[$v]=$rt[$v]=$len+2*$n; # unbounded tolerance 	  
			$U->insert($v);
			$v_ub_tag[$v]='unbounded';
		}else{ #bound vertex	   
			$lt[$v]=$len*rand(1);
			$rt[$v]=$len*rand(1);	   
			$B->insert($v);
			$v_ub_tag[$v]='bounded';
		}
	}
	
	#--- set the source and terminal target vertices
	$source=$terminal=0;	 
	while ($source==$terminal){  
		$source=int(rand($n))+1;
		$terminal=int(rand($n))+1;
	}	 
	if ($a[$source] > $a[$terminal]){  # exchange source and terminal
		$tmp=$source; $source=$terminal ; $terminal=$tmp;
	}
  
	@k_set=($source, $terminal);
	for ($v=1 ; $v <= $n ; $v++){
		$p[$v]=$p;
	}
	$p[$source]=$p[$terminal]=1; 
}

# normalized trapezoid representation of a multitolerance graph
sub normalized_trapezoid_representation {
#  bounded vertex,eg:length(b-a)=8,left tolerance lt=3 , right tolerance rt=6; let c=a+lt and let d=b-rt
#                  c*------------*b
#                  /            /
#                 /          /
#               a*--------*d  
#  unbounded vertex,eg:length(b-a)=8,tolerance t>8; let c=b and d=a
#                          / *c
#                       /
#                    /
#               d* /

	my (@key,$i);
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
	for ($v=1; $v <= $n ; $v++){
		if ($b[$v] >= $a[$v]+$lt[$v]){ # bounded vertex
			$c[$v]=$a[$v]+$lt[$v];  #construct c on top line
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
	$all_max=$i;
  
	# construct the bottom line
	%p=();# reset
	for ($v=1; $v <= $n ; $v++){
		if ($b[$v] >= $a[$v]+$lt[$v]){ # bounded vertex
			$d[$v]=$b[$v]-$rt[$v];
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
	$b_max=$i;  
}


sub sortbybvalue {
	return(-1) if ($p{$a} < $p{$b});
	return(1) if ($p{$a} > $p{$b}); 
}

sub print_multitolerance_graph {
	print "interval v[a, b]:\n";
	for ($v=1 ; $v<=$n ; $v++){
		printf(" %d[%3.1f,%3.1f]",$v,$a[$v],$b[$v]);
	}	
	print "\ntolerance v(lt,rt): \n";
	for ($v=1 ; $v<=$n ; $v++){
		if ($B->has($v)){ #bounded
			printf(" %d(%4.2f,%4.2f)",$v,$lt[$v],$rt[$v]);
		}else{ #unbounded
		  print " $v(*,*)";
		}		
	}
	print "\n";
}

sub print_normalized_trapezoid_representation {
	print "normalized trapezoid representation (*: unbounded vertex):\n";
	for ($i=0; $i < $all_max ; $i++){	  
		print " $v_tag[$i]";
		print "*" if ($ub_tag[$i] eq "unbounded");		
	}	
	print "\n";
	for ($i=0; $i < $all_max ; $i++){	  
		print " $v_tag2[$i]";
		print "*" if ($ub_tag2[$i] eq "unbounded");		
	}		
	print "\n";
}

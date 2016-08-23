#!/usr/bin/perl
#
# compute the K-terminal reliability of a d-trapezoid graph (note: test only the case of d=2)
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$n=9; 	# problem size
$q=0.5; # the failure probability of each vertex
$target_p=0.1;   # the probability that a vertex is a target vertex
$two_terminal_test=1;  # if two_terminal_test then test 2-termainl reliability else test K-terminal reliability

$m=0;	# the number of scanlines in the d-trapezoid graph
@q=(); # the failure probability of each node, target vertex v: $q[$v]=0, nontarget vertex v: $q[$v]=$q

%a=%b=%c=%d=();
@Q=();
@s_t=();# index of a scanline on the top line
@s_b=();# index of a scanline on the bottom line
@ps=(); # the partial order set; $ps[$i]: denote the set of scanlines that less then si

while ( $test++ < 20 ){ # test 20 random instances	
	$num_target=&new_g(); # create a random 2-trapezoid graph
	next if ($num_target < 2); # skip if the number of target vertices < 2
	
	print "\n== test$test: 2-trapezoid diagram: ==\n";	
	print "@top[1..$#top]\n";	# top line
	print "@bottom[1..$#bottom]\n";	# bottom line
	print "target vertices: ";
	for($v=1; $v<=$n; $v++){ # print target vertices
		print "$v " if ($q[$v]==0);			
	}
	print "\n";
	
	print "our proposed algorithm	 : ";	
	&compute_all_scanlines_and_Qs();	
	$ktr1=&compute_KTR();	
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

sub compute_KTR{	
	@prR=();
	$Q[$m+1]= Set::Scalar->new; # dummy scanline m+1
	$ps[$m+1]= Set::Scalar->new;# dummy scanline m+1
	for ($i=1 ; $i <= $m ; $i++){
		$ps[$m+1]->insert($i);   # let all scanlines be less than the dummy scanline
	}   
  
	for ($k=1; $k <= $m+1; $k++){
		$prR[$k]=1;
		foreach $j ($ps[$k]->elements) {#sj < sk        
			$tmp=1;
			for $v (($Q[$j]-$Q[$k])->elements){
				$tmp *= $q[$v];
			} 
			$prR[$k] -= $prR[$j]*$tmp;
		}
	}
	return($prR[$m+1]);
}

sub compute_all_scanlines_and_Qs {
  # compute LK=(min_a, min_c) and RK=(max_b, max_d), and the source and terminal vertices for using in brute force algorithm
	$min_a=$min_c=2*$n+1; 
	$max_b=$max_d=-1;
	$source=$terminal=0;	
	for ($v=1; $v <= $n ; $v++){	  
		if ($q[$v]==0){#v is a target vertex
			if ($a[$v] <= $min_a){
				$min_a=$a[$v];
				$source=$v;#for brute force algorithm
			}
			$min_c=$c[$v] if ($c[$v] <= $min_c);
			if ($b[$v] >= $max_b){
				$max_b=$b[$v];
				$terminal=$v;#for brute force algorithm
			}    
			$max_d=$d[$v] if ($d[$v] >= $max_d);
		}
	}

	# compute Q(s) for all scanlines between LK and RK
	$top_min=$min_a+0.5;
	$top_max=$max_b-0.5;
	$bottom_min=$min_c+0.5;
	$bottom_max=$max_d-0.5;
	$k=0;
	for ($t=$top_min; $t <= $top_max ; $t++){
		for ($b=$bottom_min; $b <= $bottom_max; $b++){
			$k++;
			$Q[$k]= Set::Scalar->new; 
			$s_t[$k]=$t; #the position of scanline k on top line
			$s_b[$k]=$b; #the position of scanline k on bottom line
			$Q[$k]= Set::Scalar->new; 
			for($i=1; $i <= $n ; $i++){              
				if (!(($b[$i] < $t && $d[$i] < $b) || ($a[$i] > $t && $c[$i] > $b))){
					$Q[$k]->insert($i);
				}
			}
		}
	}
	
	$m=$k;# m denote the number of scanlines between LK and RK
	
	#compute the partial order sets for all scanlines
	for ($i=1; $i <= $m ; $i++){
		$ps[$i]= Set::Scalar->new;     
		for ($j=1; $j <= $m ; $j++){
			next if ($i==$j);
			if (($s_t[$j] <= $s_t[$i]) && ($s_b[$j] <= $s_b[$i])){    
				$ps[$i]->insert($j);
			}
		}
	}
}

sub brute_force {
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n);
	for ($v=1; $v <= $n-1 ; $v++){
		for ($u=$v+1 ; $u <= $n ; $u++){
			if (!(($b[$v]<$a[$u] && $d[$v]<$c[$u]) || ($b[$u]<$a[$v] && $d[$u]<$c[$v]))){
				$g->add_edges([$v,$u]);
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
		my $tcg=Graph::TransitiveClosure->new($h);    
		if ($tcg->is_reachable($source, $terminal)){
			$r += $pr;
		} 
	}		
	return $r;
}

sub new_g{
	@a=@b=@c=@d=();
	@top=@bottom=();
	%p1=%p2=();
	for ($v=1; $v <=$n ; $v++){
		# top line
		$p1{"$v#a"}=rand(1);
		$p1{"$v#b"}=rand(1);
		if ($p1{"$v#a"} > $p1{"$v#b"}){#swap
			$tmp=$p1{"$v#b"};
			$p1{"$v#b"}=$p1{"$v#a"};
			$p1{"$v#a"}=$tmp;
		}
		# bottom line
		$p2{"$v#c"}=rand(1);
		$p2{"$v#d"}=rand(1);
		if ($p2{"$v#c"} > $p2{"$v#d"}){#swap
			$tmp=$p2{"$v#d"};
			$p2{"$v#d"}=$p2{"$v#c"};
			$p2{"$v#c"}=$tmp;
		}	
	}
	
	@key1 = sort {$p1{$a}<=>$p1{$b}} keys(%p1);#sort by p values from left to right
	$pi=0;
	foreach $k (@key1){#re-arrange the positions of endpoints ai and bi for all vi		
		$pi++;
		($v, $ab)=split("#",$k); 	
		$top[$pi]=$v;		
		$ab eq "a" ? $a[$v]=$pi : $b[$v]=$pi;	
	}		
	
	@key2 = sort {$p2{$a}<=>$p2{$b}} keys(%p2); #sort by p values from left to right
	$pi=0;
	foreach $k (@key2){#re-arrange the positions of endpoints ci and di for all vi		
		$pi++;
		($v, $cd)=split("#",$k); 	
		$bottom[$pi]=$v;		
		$cd eq "c" ? $c[$v]=$pi : $d[$v]=$pi;	
	}		

	# set target vertices
	
	if ($two_terminal_test){ # test 2-termnal reliability (choose the leftmost and the rightmost of trapezoids as the source and the terminal target vertices, respectively)
		$min_bd=2*$n+1; $max_ac=0;
		for ($v=1; $v<=$n ; $v++){
			$q[$v]=$q;
		  $bd=($b[$v] > $d[$v] ? $b[$v] : $d[$v]);
			if ($bd < $min_bd ){
				$min_bd=$bd;
				$source=$v;
				$next;
			}
		  $ac=($a[$v] > $c[$v] ? $c[$v] : $a[$v]);
			if ($ac > $max_ac ){
				$max_ac=$ac;
				$terminal=$v;
			}			
		}
		$q[$source]=$q[$terminal]=0;		
		$number_target=($source==$terminal? 1 : 2);		
	}else{ # test K-terminal reliability
		$number_target=0;
		for($v=1; $v <= $n ; $v++){
			if (rand(1) < $target_p){
				$q[$v]=0;#target node
				$number_target++;
			}else{
				$q[$v]=$q;#non-target node
			}
		}
	}
	return ($number_target);
}

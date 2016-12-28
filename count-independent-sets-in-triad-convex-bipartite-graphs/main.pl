#!/usr/bin/perl
#
# Count independet sets(IS), maximal independent sets(MIS), and independent perfect dominating sets(IPDS) in a triad convex bipartite graph
#
# by Min-Sheng Lin
#
use Set::Scalar;
use Graph;
$|=1;

#globals
$nv=3;               # n=nv+nh <==> |X|=|V|+|H|; V: the vertices on the vertical path, H: the vertices on the horizontal path
$nh=5;
$m=4;                # |Y|     
 
$n=$nv+$nh; # problem size

@adj=();  # the adjacent matrix 
@N=(); %N=(); # neighbor 
@l=@lx=();  # $l[b] is the lefttmost 'a' point connecting 'b'
@r=@rx=();  # $r[b] is the rightmost 'a' point connecting 'b'
@t=@tx=();  # $t[b] is the top 'a' point connecting 'b'
@b=@bx=();  # $b[b] is the bottom 'a' point connecting 'b'
$xp=0;    #  xp(ht in the paper) is the vertex on h-path that adjoins the bottom vertex vq on v-path in T.

while ( $test++ < 5 ){ # test 20 random instances	  	  
	&new_g(); #generate a triad convex tree bipartite randomly  
	print "\n== test$test: triad convex bipartite graph: |Xh|=$nh, |Xv|=$nv, |Y|=$m, xp=$xp\ ==\n";
	&print_g();	
	print "\n";

	print "our proposed algorithm	 : ";	
	($IS1)=&compute_triad_IS(); 
	($MIS1, $IPDS1)=&compute_triad_MIS_IPDS(); 
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


sub print_g{
	for ($b=1 ; $b <= $m ; $b++){		
		for (@a=(),$a=$l[$b]; $a<=$r[$b] and 1<=$a and $a<=$n ; $a++){
			push @a,$a;
		}		
		print " Nh[$b]={",join(",",@a),"},";
    
		for (@a=(),$a=$t[$b]; $a<=$b[$b] and 1<=$a and $a<=$n ; $a++){
			push @a,$a;
		}	
		print " Nv[$b]={",join(",",@a),"};";		
	}
	print "\n";
}

sub compute_triad_IS{  
	my (@IS1,@IS2,$i,$j,$k,$s,$t,$vset,$hset,$y,$y1,$IS);
	@IS1=@IS2=(); $IS=0;
	#-- G1: vertical
	$IS1[0]=1;  
	for ($i=0 ; $i <=$nv ; $i++){
		for ($k=$i+1 ; $k <=$nv+1 ; $k++){	    
			#-- compute y1 for G1		
			$vset= Set::Scalar->new;
			for ($s=$i+1; $s<=$k-1 ; $s++){
				$vset->insert("v$s"); # $vset={v|vi < v < vk}
			}  
			$y1=Set::Scalar->new;
			for ($y=1 ; $y<=$m ; $y++){
				if ( $N[$y]->is_subset($vset) ){
					$y1->insert($y);
				}
			}
			
			$IS1[$k] += $IS1[$i]*(2**($y1->size));	# Eq. (8) in the paper
		}
	}
	
	#-- horizontal -->
	for ($j=0; $j<=$nv ; $j++){
		@IS2=(); # reset
		$IS2[0]=1;    	
		for ($i=0 ; $i <=$nh ; $i++){
			for ($k=$i+1 ; $k <= $nh+1 ; $k++){	    
				#-- compute y2 for G2,  
				$hset= Set::Scalar->new; # $hset={u|hi <j u <j hk}
				for ($s=$i+1; $s<=$k-1 ; $s++){
					$hset->insert("h$s");
				}
				if ($i<=$xp and $xp < $k){
					for ($s=$j+1; $s<=$nv ; $s++){
						$hset->insert("v$s");
					}  	
				}		
				$y2=Set::Scalar->new;
				for ($y=1 ; $y<=$m ; $y++){
					if ( $N[$y]->is_subset($hset) ){
						$y2->insert($y);
					}
				}
			
				$IS2[$k] += $IS2[$i]*(2**($y2->size)); # Eq. (9) in the paper
			}
		}	
		
		$IS += $IS1[$j]*$IS2[$nh+1]; # Eq. (7) in the paper
	}
	return($IS);
}

sub compute_triad_MIS_IPDS {
	my (@MIS1,@MIS2, @IPDS1,@IPDS2, $i,$j,$k,$s,$t,$vset,$hset,$y,$y1,$MIS,$IPDS);
	@MIS1=@MIS2=(); $MIS=0;  
	@IPDS1=@IPDS2=(); $IPDS=0;  
	#-- G1: vertical
	$MIS1[0]=1; $IPDS1[0]=1;
	for ($i=0 ; $i <=$nv ; $i++){
		for ($k=$i+1 ; $k <= $nv+1 ; $k++){	    
			$vset= Set::Scalar->new;
			for ($s=$i+1; $s<=$k-1 ; $s++){
				$vset->insert("v$s"); # $vset={v|vi < v < vk}
			}
			
			$union_Ny=Set::Scalar->new;
			$N_all_size=0;
			for ($y=1 ; $y<=$m ; $y++){
				if ( $N[$y]->is_subset($vset) ){ # y is in Y1
					$union_Ny += $union_Ny + $N[$y]; # for MIS
					$N_all_size += $N[$y]->size; # for IPDS
				}
			}
			if ($union_Ny == $vset){
				$MIS1[$k] += $MIS1[$i];   # Eq. (16) in the paper				
				$xx1=$N{"v$i"}*$N{"v$k"};
				if ($N_all_size ==  $vset->size and $xx1->is_empty){ #conditions (1) and (2) in Property 3 in the paper
					$IPDS1[$k]+= $IPDS1[$i];  		  
				}
			}	
		}
	}

	#---- horizontal --->
	for ($j=0; $j <=$nv ; $j++){
		@MIS2=(); @IPDS2=();
		$MIS2[0]=1; $IPDS2[0]=1;   	 
		for ($i=0 ; $i <=$nh ; $i++){
			for ($k=$i+1 ; $k <= $nh+1 ; $k++){	    				
				$hset= Set::Scalar->new; # $hset={u|hi <j u <j hk}
				for ($s=$i+1; $s<=$k-1 ; $s++){
					$hset->insert("h$s"); 
				}
				if ($i<=$xp and $xp < $k){
					for ($s=$j+1; $s<=$nv ; $s++){
						$hset->insert("v$s");
					}
				}				
				$union_Ny=Set::Scalar->new;
				$N_all_size=0;
				for ($y=1 ; $y<=$m ; $y++){
					if ( $N[$y]->is_subset($hset) ){
						$union_Ny += $union_Ny + $N[$y]; # for MIS
						$N_all_size += $N[$y]->size; # for IPDS
					}
				}
				if ($union_Ny == $hset){
					$MIS2[$k]+= $MIS2[$i]; # Eq. (17) in the paper
					$xx1=$N{"h$i"}*$N{"h$k"}; $xx2=$N{"h$i"}*$N{"v$j"}; $xx3=$N{"h$k"}*$N{"v$j"};
					if ($N_all_size == $hset->size and $xx1->is_empty and $xx2->is_empty and $xx3->is_empty){#conditions (1), (2), (3) and (4) in Property 4 in the paper
						$IPDS2[$k]+= $IPDS2[$i];  
					}
				}
			}
		}
		$MIS+=$MIS1[$j]*$MIS2[$nh+1];
		$IPDS+=$IPDS1[$j]*$IPDS2[$nh+1];
	}
	return($MIS,$IPDS);
}

#-------------------------------------
#  triad convex tree bipartite graph :
#  partition the vertices of X into two parts: horizontal line(h-path) and vertical line(v-path)
#  for each vertex b of Y, the vertices of N(b) form a subtree in the triad convex tree, e.g.:
#           v1=8
#           v2=9
#           v3=10
#  h1 h2 h3 h4 h5 h6 h7
#   1  2  3  4  5  6  7
#
sub new_g {   #create a random triad convex tree bipartite graph  
	my($p1,$p2,$p3,@p,$b,$u);	
	@adj=();  @N=(); %N=();
	@lx=@rx=@tx=@bx=();
	@l=@r=@t=@b=();  
	# note: n=nh+nv;  |X|=n  and |Y|=m

	$xp=int(rand($nh))+1; #e.g. xp=4 in the above example. note: xp denote 'ht' in the paper

	for ($u=1 ; $u<=$m ; $u++){  # for each u in Y, randomly pick three points in X
		$p0=int(rand($n))+1;  # 1~n
		$p1=int(rand($n))+1;  # 1~n
		$p2=int(rand($n))+1;  # 1~n
		@p=sort($p0,$p1,$p2); # sorting: p0 <= p1 <= p2

		# setup the left, right, top, bottom for each vertex u according to p0, p1, p2
		if ($p[0] > $nh){  # all p0, p1, p2 are on v-path
			$t[$u]=$p[0]; $b[$u]=$p[2];  # skip p1
			$l[$u]=$nh+1; $r[$u]=0; # no neighbor of u is on h-path; checking: let l(u) be maximum and r(u) be minimum	   
			$tx[$u]=$t[$u]-$nh; $bx[$u]=$b[$u]-$nh;
			$lx[$u]=$l[$u];     $rx[$u]=$r[$u];
		}elsif ($p[1] > $nh){ # p0 is on h-path; p1 and p2 are on v-path
			$t[$u]=$p[1]; $b[$u]=$nh+$nv; # force neighbor of u connecting to v(n+1) (virtual node)
			if ($p[0] < $xp){ # p0 is on the left of x
				$l[$u]=$p[0]; $r[$u]=$xp ; # force neighbor of u connecting to  x;
			}else{ # p0 is on the right of x
				$l[$u]=$xp; $r[$u]=$p[0]; # force neighbor of u connecting to  x
			}
			$tx[$u]=$t[$u]-$nh; $bx[$u]=$b[$u]-$nh;
			$lx[$u]=$l[$u];     $rx[$u]=$r[$u];	   
		}elsif ($p[2] > $nh){ # p0,p1 are on h-path and p2 is on v-path
			$t[$u]=$p[2]; $b[$u]=$nh+$nv;# force neighbor of u connecting to  v(n+1) (virtual node)	  
			$l[$u]=$p[0]; $r[$u]=$p[1];  # initial	   
			$l[$u]=$xp if ($xp < $p[0]); # force neighbor of u connecting to  x	   
			$r[$u]=$xp if ($xp > $p[1]); # force neighbor of u connecting to  x	   	   	   
			$tx[$u]=$t[$u]-$nh; $bx[$u]=$b[$u]-$nh;
			$lx[$u]=$l[$u];     $rx[$u]=$r[$u];	   
		}else { # all p0, p1, p2 are on h-path
			$t[$u]=$nh+$nv+1; $b[$u]=0; # no neighbor of u is on v-path; checking: let t[u] be maximum and b[u] be minimum
			$l[$u]=$p[0]; $r[$u]=$p[2];  # skip p1	   
			$tx[$u]=$t[$u]-$nh; $bx[$u]=0;
			$lx[$u]=$l[$u];     $rx[$u]=$r[$u];	   
		}	
	}# for each u in Y

	# compute N[b] for each b in Y, and N{hi}, N{vi} for each hi,vi in X
	for ($i=0 ; $i <= $nh+1 ; $i++){
		$N{"h$i"}= Set::Scalar->new;   
	}
	for ($i=0 ; $i <= $nv+1 ; $i++){
		$N{"v$i"}= Set::Scalar->new;   
	}
	for ($b=1; $b <=$m ; $b++){  
		$N[$b]= Set::Scalar->new;   
		for ($a=$l[$b]; $a <= $r[$b] and 1<=$a and $a<=$n ; $a++){
			$adj[$a][$b]=1; # Note:if a ==0 or a==n+1, then a is a virtual node and skip  	 
			$N[$b]->insert("h$a");
			$N{"h$a"}->insert($b);
		}# for a	
		for ($a=$t[$b]; $a <= $b[$b] and 1<=$a and $a<=$n ; $a++){
			$adj[$a][$b]=1; # Note:if a ==0 or a==n+1, then a is a virtual node and skip  	 
			$ax=$a-$nh;
			$N[$b]->insert("v$ax");
			$N{"v$ax"}->insert($b);
		}
	}
}

sub brute_force{
	return if ($n+$m > 15);
	$g = Graph::Undirected->new();
	$g->add_vertices(1..$n+$m);
	%edge=();
	for ($a=1; $a<=$n; $a++){
		for ($b=1; $b<=$m; $b++){      
			if ($adj[$a][$b]){
				$g->add_edges([$a,$n+$b]);  #b is shifted n positions
			}
		}
	}

	$max=2**$g->vertices-1;
	@vc_set=();
	@vc_set = map { Set::Scalar->new() } 0..$max;

	#for checking independent perfect dominating sets
	my $all_v= Set::Scalar->new(1..$n+$m); # all vertices
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
						if ($g->has_edge($i,$u)){ # u and i are adjacent
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

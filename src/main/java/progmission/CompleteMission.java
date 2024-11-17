package progmission;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Iterator;

import org.apache.commons.lang3.ObjectUtils.Null;
import org.slf4j.Logger;

import fr.cnes.sirius.patrius.assembly.models.SensorModel;
import fr.cnes.sirius.patrius.attitudes.Attitude;
import fr.cnes.sirius.patrius.attitudes.AttitudeLaw;
import fr.cnes.sirius.patrius.attitudes.AttitudeLawLeg;
import fr.cnes.sirius.patrius.attitudes.AttitudeLeg;
import fr.cnes.sirius.patrius.attitudes.AttitudeProvider;
import fr.cnes.sirius.patrius.attitudes.ConstantSpinSlew;
import fr.cnes.sirius.patrius.attitudes.StrictAttitudeLegsSequence;
import fr.cnes.sirius.patrius.attitudes.TargetGroundPointing;
import fr.cnes.sirius.patrius.events.CodedEvent;
import fr.cnes.sirius.patrius.events.CodedEventsLogger;
import fr.cnes.sirius.patrius.events.GenericCodingEventDetector;
import fr.cnes.sirius.patrius.events.Phenomenon;
import fr.cnes.sirius.patrius.events.postprocessing.AndCriterion;
import fr.cnes.sirius.patrius.events.postprocessing.ElementTypeFilter;
import fr.cnes.sirius.patrius.events.postprocessing.Timeline;
import fr.cnes.sirius.patrius.events.sensor.SensorVisibilityDetector;
import fr.cnes.sirius.patrius.frames.FramesFactory;
import fr.cnes.sirius.patrius.frames.TopocentricFrame;
import fr.cnes.sirius.patrius.math.ode.events.EventHandler.Action;
import fr.cnes.sirius.patrius.math.util.MathLib;
import fr.cnes.sirius.patrius.propagation.analytical.KeplerianPropagator;
import fr.cnes.sirius.patrius.propagation.events.ConstantRadiusProvider;
import fr.cnes.sirius.patrius.propagation.events.EventDetector;
import fr.cnes.sirius.patrius.propagation.events.ThreeBodiesAngleDetector;
import fr.cnes.sirius.patrius.propagation.events.VariableRadiusProvider;
import fr.cnes.sirius.patrius.math.geometry.euclidean.threed.Vector3D;
import fr.cnes.sirius.patrius.time.AbsoluteDate;
import fr.cnes.sirius.patrius.time.AbsoluteDateInterval;
import fr.cnes.sirius.patrius.time.AbsoluteDateIntervalsList;
import fr.cnes.sirius.patrius.utils.exception.PatriusException;
import java.awt.Desktop;
import reader.Site;
import utils.ConstantsBE;
import utils.LogUtils;
import utils.ProjectUtils;
// à trier
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Collections;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.slf4j.Logger;

import reader.Site;
import reader.SitesReader;
import utils.ConstantsBE;
import utils.LogUtils;
import utils.VTSTools;

import com.opencsv.exceptions.CsvValidationException;

import fr.cnes.sirius.addons.patriusdataset.PatriusDataset;
import fr.cnes.sirius.patrius.attitudes.Attitude;
import fr.cnes.sirius.patrius.attitudes.AttitudeLawLeg;
import fr.cnes.sirius.patrius.attitudes.AttitudeLeg;
import fr.cnes.sirius.patrius.attitudes.StrictAttitudeLegsSequence;
import fr.cnes.sirius.patrius.attitudes.TargetGroundPointing;
import fr.cnes.sirius.patrius.bodies.CelestialBody;
import fr.cnes.sirius.patrius.bodies.CelestialBodyFactory;
import fr.cnes.sirius.patrius.bodies.ExtendedOneAxisEllipsoid;
import fr.cnes.sirius.patrius.events.Phenomenon;
import fr.cnes.sirius.patrius.events.postprocessing.Timeline;
import fr.cnes.sirius.patrius.frames.Frame;
import fr.cnes.sirius.patrius.frames.FramesFactory;
import fr.cnes.sirius.patrius.frames.TopocentricFrame;
import fr.cnes.sirius.patrius.frames.transformations.Transform;
import fr.cnes.sirius.patrius.math.geometry.euclidean.threed.Vector3D;
import fr.cnes.sirius.patrius.math.util.FastMath;
import fr.cnes.sirius.patrius.math.util.MathLib;
import fr.cnes.sirius.patrius.orbits.CircularOrbit;
import fr.cnes.sirius.patrius.orbits.Orbit;
import fr.cnes.sirius.patrius.orbits.PositionAngle;
import fr.cnes.sirius.patrius.orbits.pvcoordinates.PVCoordinates;
import fr.cnes.sirius.patrius.propagation.BoundedPropagator;
import fr.cnes.sirius.patrius.propagation.analytical.KeplerianPropagator;
import fr.cnes.sirius.patrius.time.AbsoluteDate;
import fr.cnes.sirius.patrius.time.AbsoluteDateInterval;
import fr.cnes.sirius.patrius.time.TimeScale;
import fr.cnes.sirius.patrius.time.TimeScalesFactory;
import fr.cnes.sirius.patrius.utils.Constants;
import fr.cnes.sirius.patrius.utils.exception.PatriusException;
import fr.cnes.sirius.patrius.utils.exception.PropagationException;

/**
 * This class implements the context of an Earth Observation mission.
 *
 * @author herberl
 */
public class CompleteMission extends SimpleMission {

	/**
	 * Logger for this class.
	 */
	private final Logger logger = LogUtils.GLOBAL_LOGGER;

	/**
	 * Maximum checking interval (s) for the event detection during the orbit
	 * propagation.
	 */
	public static final double MAXCHECK_EVENTS = 120.0;

	/**
	 * Default convergence threshold (s) for the event computation during the orbit
	 * propagation.
	 */
	public static final double TRESHOLD_EVENTS = 1.e-4;

	/**
	 * This {@link Map} will be used to enumerate each site access {@link Timeline},
	 * that is to say a {@link Timeline} with access windows respecting all
	 * observation conditions. This object corresponds to the access plan, which
	 * will be computed in the computeAccessPlan() method.
	 */
	private final Map<Site, Timeline> accessPlan;

	/**
	 * This {@link Map} will be used to enumerate each site's programmed
	 * observation. We suggest to use an {@link AttitudeLawLeg} to encapsulate the
	 * guidance law of each observation. This object corresponds to the observation
	 * plan, which will be computed in the computeObservationPlan() method.
	 */
	private final Map<Site, AttitudeLawLeg> observationPlan;

	/**
	 * {@link StrictAttitudeLegsSequence} representing the cinematic plan during the
	 * whole mission horizon. Each {@link AttitudeLeg} corresponds to a diffrent
	 * attitude law : either nadir pointing, target pointing or a slew between two
	 * laws. This object corresponds to the cinematic plan, which will be computed
	 * in the computeCinematicPlan() method.
	 */
	private final StrictAttitudeLegsSequence<AttitudeLeg> cinematicPlan;

	/**
	 * Constructor for the {@link CompleteMission} class.
	 *
	 * @param missionName   Name of the mission
	 * @param numberOfSites Number of target {@link Site} to consider, please give a
	 *                      number between 1 and 100.
	 * @throws PatriusException      Can be raised by Patrius when building
	 *                               particular objects. Here it comes from
	 *                               {@link FramesFactory}
	 * @throws IllegalStateException if the mission horizon is too short
	 */
	public CompleteMission(final String missionName, int numberOfSites) throws PatriusException {

		// Since this class extends the SimpleMission class, we need to use the super
		// constructor to instantiate our instance of CompleteMission. All the
		// attributes of the super class will be instantiated during this step.
		super(missionName, numberOfSites);

		// Initialize the mission plans with empty maps. You will fill those HashMaps in
		// the "compute****Plan()" methods.
		this.accessPlan = new HashMap<>();
		this.observationPlan = new HashMap<>();
		this.cinematicPlan = new StrictAttitudeLegsSequence<>();

	}

	/**
	 * A hash based on all the constants of the BE. This hash is unique and ensures
	 * we get the right filename for a given {@link Site} and a given set of
	 * {@link ConstantsBE} parameters. It is used in the names of the files
	 * containing the serialized accesses for all {@link Site}.
	 *
	 */
	private final static int hashConstantBE;

	/**
	 * [DO NOT MODIFY THIS METHOD]
	 * 
	 * This block of code is static, shared by all instances of CompleteMission. It
	 * is executed only once when the class is first instantiated, to produce an
	 * unique hash which encodes the whole constants of the BE in one single code.
	 * You don't have to (and must not) modify this code if you want to benefit from
	 * automatic serialization and reading of you access Timelines.
	 */
	static {
		// Creating an unique hash code to be used for serialization
		int hash = 17;

		long doubleBits;
		int doubleHash;

		// The hash code depends from all the parameters from a given simulation : start
		// and end date and all the ConstantBE values. We build a hashcode from all
		// those values converting them as int

		// Start and end dates
		hash = 31 * hash + ConstantsBE.START_DATE.hashCode();
		hash = 31 * hash + ConstantsBE.END_DATE.hashCode();

		// ConstantBE values
		double doubles[] = new double[] { ConstantsBE.ALTITUDE, ConstantsBE.INCLINATION, ConstantsBE.MEAN_ECCENTRICITY,
				ConstantsBE.ASCENDING_NODE_LONGITUDE, ConstantsBE.POINTING_CAPACITY, ConstantsBE.SPACECRAFT_MASS,
				ConstantsBE.MAX_SUN_INCIDENCE_ANGLE, ConstantsBE.MAX_SUN_PHASE_ANGLE, ConstantsBE.INTEGRATION_TIME,
				ConstantsBE.POINTING_AGILITY_DURATIONS[0], ConstantsBE.POINTING_AGILITY_DURATIONS[1],
				ConstantsBE.POINTING_AGILITY_DURATIONS[2], ConstantsBE.POINTING_AGILITY_DURATIONS[3],
				ConstantsBE.POINTING_AGILITY_DURATIONS[4], ConstantsBE.POINTING_AGILITY_ROTATIONS[0],
				ConstantsBE.POINTING_AGILITY_ROTATIONS[1], ConstantsBE.POINTING_AGILITY_ROTATIONS[2],
				ConstantsBE.POINTING_AGILITY_ROTATIONS[3], ConstantsBE.POINTING_AGILITY_ROTATIONS[4], MAXCHECK_EVENTS,
				TRESHOLD_EVENTS };
		for (Double d : doubles) {
			doubleBits = Double.doubleToLongBits(d);
			doubleHash = (int) (doubleBits ^ (doubleBits >>> 32));
			hash = 31 * hash + doubleHash;
		}

		// Finally assigning the current simulation hashConstantBE value
		hashConstantBE = hash;
	}

	/**
	 * [COMPLETE THIS METHOD TO ACHIEVE YOUR PROJECT]
	 * 
	 * This method should compute the input {@link Site}'s access {@link Timeline}.
	 * That is to say the {@link Timeline} which contains all the {@link Phenomenon}
	 * respecting the access conditions for this site : good visibility + corrrect
	 * illumination of the {@link Site}.
	 * 
	 * For that, we suggest you create as many {@link Timeline} as you need and
	 * combine them with logical gates to filter only the access windows phenomenon.
	 * 
	 * @param targetSite Input target {@link Site}
	 * @return The {@link Timeline} of all the access {@link Phenomenon} for the
	 *         input {@link Site}.
	 * @throws PatriusException If a {@link PatriusException} occurs.
	 */
	private Timeline createSiteAccessTimeline(Site targetSite) throws PatriusException {
		/**
		 * Step 1 :
		 * 
		 * Create one Timeline per phenomenon you want to monitor.
		 */
		/*
		 * Use the createSiteXTimeline method to create a custom Timeline. More
		 * indication are given inside the method. Note that you will have to code one
		 * method per constraint, for example the method createSiteVisibilityTimeline
		 * for visibility constraint and createSiteIlluminationTimeline for illumination
		 * constraint. All the methods you code can be coded using the given
		 * createSiteXTimeline method as a basis.
		 */
		final Timeline timeline1 = createSiteVisibilityTimeline(targetSite);
		final Timeline timeline2 = createSiteIlluminationTimeline(targetSite);
		final Timeline timeline3 = createSiteDazzlingTimeline(targetSite);

		/**
		 * Step 2 :
		 * 
		 * Combine the timelines with logical gates and retrieve only the access
		 * conditions through a refined Timeline object.
		 * 
		 * For that, you can use the classes in the events.postprocessing module : for
		 * example, the AndCriterion or the NotCriterion.
		 * 
		 * Finally, you can filter only the Phenomenon matching a certain condition
		 * using the ElementTypeFilter
		 */
		/*
		 * Code your logical operations on Timeline objects and filter only the access
		 * Phenomenon (gathering all constraints you need to define an access condition)
		 * below.
		 */
		// Combining all Timelines
		// Creating a global Timeline containing all phenomena, this Timeline will be
		// filtered and processed to that only the access Phenomennon remain, this is
		// our siteAccessTimeline
		final Timeline siteAccessTimeline = new Timeline(
				new AbsoluteDateInterval(this.getStartDate(), this.getEndDate()));
		// Adding the phenomena of all the considered timelines
		for (final Phenomenon phenom : timeline1.getPhenomenaList()) {
			siteAccessTimeline.addPhenomenon(phenom);
		}
		for (final Phenomenon phenom : timeline2.getPhenomenaList()) {
		 	siteAccessTimeline.addPhenomenon(phenom);
		}
		for (final Phenomenon phenom : timeline3.getPhenomenaList()) {
			siteAccessTimeline.addPhenomenon(phenom);
	   	}

		// ProjectUtils.printTimeline(timeline1);
		// ProjectUtils.printTimeline(timeline2);
		// ProjectUtils.printTimeline(timeline3);

		// Define and use your own criteria, here is an example (use the right strings
		// defined when naming the phenomenon in the GenericCodingEventDetector)
		final AndCriterion andCriterion = new AndCriterion("Visibility phenomenon", "Illumination phenomenon",
				"Visibility and Illumination", "Combinaison of Visibilisation and Illumination phenomena");
		andCriterion.applyTo(siteAccessTimeline);
		final AndCriterion andCriterion2 = new AndCriterion("Visibility and Illumination", "Dazzling phenomenon",
				"Visibility and Illumination and Dazzling", "Combinaison of Visibilisation and Illumination and Dazzling phenomena");
		// Applying our criterion adds all the new phenonmena inside the global timeline
		andCriterion2.applyTo(siteAccessTimeline);

		// Then create an ElementTypeFilter that will filter all phenomenon not
		// respecting the input condition you gave it
		final ElementTypeFilter obsConditionFilter = new ElementTypeFilter("Visibility and Illumination and Dazzling", false);
		// Finally, we filter the global timeline to keep only X1 AND X2 phenomena
		obsConditionFilter.applyTo(siteAccessTimeline);

		/*
		 * Now make sure your globalTimeline represents the access Timeline for the
		 * input target Site and it's done ! You can print the Timeline using the
		 * utility module of the BE as below
		 */

		// Log the final access timeline associated to the current target
		logger.info("\n" + targetSite.getName());
		// ProjectUtils.printTimeline(siteAccessTimeline);

		return siteAccessTimeline;
	}

	/**
	 * Compute a {@link Timeline} object which encapsulates all the visibility 
	 * {@link Phenomenon} relative to the input target {@link Site}.
	 * 
	 * @param targetSite Input target {@link Site}
	 * @return The {@link Timeline} containing all the {@link Phenomenon} relative
	 *         to the visibility phenomenon.
	 * @throws PatriusException If a {@link PatriusException} occurs when creating
	 *                          the {@link Timeline}.
	 */

	private Timeline createSiteVisibilityTimeline(Site targetSite) throws PatriusException {
		// Creating the visibility timeline
		final EventDetector constraintVisibilityDetector = createConstraintVisibilityDetector(targetSite);
		KeplerianPropagator propagator = this.createDefaultPropagator();
		propagator.addEventDetector(constraintVisibilityDetector);

		final GenericCodingEventDetector codingEventVisibilityDetector = new GenericCodingEventDetector(constraintVisibilityDetector,
				"Event starting the Visibility phenomenon", "Event ending the Visibility phenomenon", true, "Visibility phenomenon");
		final CodedEventsLogger eventVisibilityLogger = new CodedEventsLogger();
		final EventDetector eventVisibilityDetector = eventVisibilityLogger.monitorDetector(codingEventVisibilityDetector);
		// Then you add your logger to the propagator, it will monitor the event coded
		// by the codingEventDetector
		propagator.addEventDetector(eventVisibilityDetector);

		// Finally propagating the orbit
		propagator.propagate(this.getStartDate(), this.getEndDate());

		// Creating a Timeline to process the events : we are going to define one
		// visibility Phenomenon by couple of events "start -> end" (linked to the
		// increase and decrease of the g function of the visibility detector)
		final Timeline phenomenonVisibilityTimeline = new Timeline(eventVisibilityLogger,
				new AbsoluteDateInterval(this.getStartDate(), this.getEndDate()), null);

		return phenomenonVisibilityTimeline;
	}

	/**
	 * Compute a {@link Timeline} object which encapsulates all the illumination 
	 * {@link Phenomenon} relative to the input target {@link Site}.
	 * 
	 * @param targetSite Input target {@link Site}
	 * @return The {@link Timeline} containing all the {@link Phenomenon} relative
	 *         to the illumination phenomenon.
	 * @throws PatriusException If a {@link PatriusException} occurs when creating
	 *                          the {@link Timeline}.
	 */

	private Timeline createSiteIlluminationTimeline(Site targetSite) throws PatriusException {
		// Create the illumination timeline
		final EventDetector constraintIlluminationDetector = createConstraintIlluminationDetector(targetSite);
		KeplerianPropagator propagator = this.createDefaultPropagator();
		propagator.addEventDetector(constraintIlluminationDetector);

		final GenericCodingEventDetector codingEventIlluminationDetector = new GenericCodingEventDetector(constraintIlluminationDetector,
				"Event starting the Illumination phenomenon", "Event ending the Illumination phenomenon", true, "Illumination phenomenon");
		final CodedEventsLogger eventIlluminationLogger = new CodedEventsLogger();
		final EventDetector eventIlluminationDetector = eventIlluminationLogger.monitorDetector(codingEventIlluminationDetector);
		// Then you add your logger to the propagator, it will monitor the event coded
		// by the codingEventDetector
		propagator.addEventDetector(eventIlluminationDetector);

		// Finally propagating the orbit
		propagator.propagate(this.getStartDate(), this.getEndDate());

		// Creating a Timeline to process the events : we are going to define one
		// visibility Phenomenon by couple of events "start -> end" (linked to the
		// increase and decrease of the g function of the visibility detector)
		final Timeline phenomenonIlluminationTimeline = new Timeline(eventIlluminationLogger,
				new AbsoluteDateInterval(this.getStartDate(), this.getEndDate()), null);

		return phenomenonIlluminationTimeline;
	}

	/**
	 * Compute a {@link Timeline} object which encapsulates all the dazzling 
	 * {@link Phenomenon} relative to the input target {@link Site}.
	 * 
	 * @param targetSite Input target {@link Site}
	 * @return The {@link Timeline} containing all the {@link Phenomenon} relative
	 *         to the dazzling phenomenon.
	 * @throws PatriusException If a {@link PatriusException} occurs when creating
	 *                          the {@link Timeline}.
	 */

	private Timeline createSiteDazzlingTimeline(Site targetSite) throws PatriusException {
		// Creating the dazzling timeline
		final EventDetector constraintDazzlingDetector = createConstraintDazzlingDetector(targetSite);
		KeplerianPropagator propagator = this.createDefaultPropagator();
		propagator.addEventDetector(constraintDazzlingDetector);

		final GenericCodingEventDetector codingEventDazzlingDetector = new GenericCodingEventDetector(constraintDazzlingDetector,
				"Event starting the Dazzling phenomenon", "Event ending the Dazzling phenomenon", false, "Dazzling phenomenon");
		//false because the g function which represents the "beginning" of the associated phenomenon is reversed.1A
		final CodedEventsLogger eventDazzlingLogger = new CodedEventsLogger();
		final EventDetector eventDazzlingDetector = eventDazzlingLogger.monitorDetector(codingEventDazzlingDetector);
		// Then you add your logger to the propagator, it will monitor the event coded
		// by the codingEventDetector
		propagator.addEventDetector(eventDazzlingDetector);

		// Finally propagating the orbit
		propagator.propagate(this.getStartDate(), this.getEndDate());

		// Creating a Timeline to process the events : we are going to define one
		// visibility Phenomenon by couple of events "start -> end" (linked to the
		// increase and decrease of the g function of the visibility detector)
		final Timeline phenomenonDazzlingTimeline = new Timeline(eventDazzlingLogger,
				new AbsoluteDateInterval(this.getStartDate(), this.getEndDate()), null);

		return phenomenonDazzlingTimeline;
	}

	/**
	 * Create the visibility detector
	 * 
	 * @return An {@link SensorVisibilityDetector} answering the visibility constraint
	 */
	private EventDetector createConstraintVisibilityDetector(Site targetSite) throws PatriusException {
		// Get sensor, add masking body and set main target
		SensorModel sensor = new SensorModel(this.getSatellite().getAssembly(), this.getSatellite().SENSOR_NAME);
		sensor.addMaskingCelestialBody(this.getEarth());
		TopocentricFrame target = new TopocentricFrame(this.getEarth(), targetSite.getPoint(), targetSite.getName());
		ConstantRadiusProvider radius = new ConstantRadiusProvider(0.0);
		sensor.setMainTarget(target, radius);
		EventDetector.Action action_continue = EventDetector.Action.CONTINUE;
		// Creating the sun incidence angle detector
		SensorVisibilityDetector visibilityDetector = new SensorVisibilityDetector(sensor, MAXCHECK_EVENTS, TRESHOLD_EVENTS, action_continue, action_continue);
		return visibilityDetector;
	}

	/**
	 * Create the illumination detector
	 * 
	 * @return An {@link ThreeBodiesAngleDetector} answering the sun illumination constraint
	 */
	private EventDetector createConstraintIlluminationDetector(Site targetSite) throws PatriusException {
		TopocentricFrame target = new TopocentricFrame(this.getEarth(), targetSite.getPoint(), targetSite.getName());
		EventDetector.Action action_continue = EventDetector.Action.CONTINUE;
		ThreeBodiesAngleDetector sunIlluminationDetector = new ThreeBodiesAngleDetector(this.getEarth(), target, this.getSun(),
			Math.PI - MathLib.toRadians(ConstantsBE.MAX_SUN_INCIDENCE_ANGLE), MAXCHECK_EVENTS, TRESHOLD_EVENTS, action_continue);
		// We used the formula pi-MAX_SUN_INCIDENCE_ANGLE because the first vector points to the center of the Earth, while we want to have the normal vector to the anticenter.
		return sunIlluminationDetector; 
	}

	/**
	 * Create the dazzling detector
	 * 
	 * @return An {@link ThreeBodiesAngleDetector} answering the dazzling constraint
	 */
	private EventDetector createConstraintDazzlingDetector(Site targetSite) throws PatriusException {
		TopocentricFrame target = new TopocentricFrame(this.getEarth(), targetSite.getPoint(), targetSite.getName());
		EventDetector.Action action_continue = EventDetector.Action.CONTINUE;
		ThreeBodiesAngleDetector dazzlingDetector = new ThreeBodiesAngleDetector(this.createDefaultPropagator(), 
		target, this.getSun(), MathLib.toRadians(ConstantsBE.MAX_SUN_PHASE_ANGLE), MAXCHECK_EVENTS, TRESHOLD_EVENTS, action_continue);
		return dazzlingDetector; 
	}
	

	/** 
	 * Compute the access plan.
	 * 
	 * @return the sites access plan with one {@link Timeline} per {@link Site}
	 * @throws PatriusException If a {@link PatriusException} occurs during the
	 *                          computations
	 */
	public Map<Site, Timeline> computeAccessPlan() throws PatriusException {

		logger.info("============= Computing Access Plan =============");
		int length = this.getSiteList().size();

		for (int i = 0; i<length; i++) {
			final Site targetSite = this.getSiteList().get(i);
			logger.info(" Site : " + targetSite.getName());

			// Checking if the Site access Timeline has already been serialized or not
			final String filename = generateSerializationName(targetSite, hashConstantBE);
			File file = new File(filename);
			boolean loaded = false;

			// If the file exist for the current Site, we try to load its content
			if (file.exists()) {
				try {
					// Load the timeline from the file and add it to the accessPlan
					final Timeline siteAccessTimeline = loadSiteAccessTimeline(filename);
					this.accessPlan.put(targetSite, siteAccessTimeline);
					ProjectUtils.printTimeline(siteAccessTimeline);
					loaded = true; // the Site has been loaded, no need to compute the access again
					logger.info(filename + "has been loaded successfully!");
				} catch (ClassNotFoundException | IOException e) {
					logger.warn(filename + " could not be loaded !");
					logger.warn(e.getMessage());
				}
			}

			// If it was not serialized or if loading has failed, we need to compute and
			// serialize the site access Timeline
			if (!loaded) {
				logger.info(targetSite.getName() + " has not been serialized, launching access computation...");
				// Computing the site access Timeline
				final Timeline siteAccessTimeline = createSiteAccessTimeline(targetSite);
				this.accessPlan.put(targetSite, siteAccessTimeline);
				ProjectUtils.printTimeline(siteAccessTimeline);

				try {
					// Serialize the timeline for later reading
					serializeSiteAccessTimeline(filename, siteAccessTimeline);
					logger.info(filename + " has been serialized successfully !");
				} catch (IOException e) {
					logger.warn(filename + " could not be serialized !");
					logger.warn(e.getMessage());
				}
			}
		}
		return this.accessPlan;
	}

	public double getIncidence(AbsoluteDate date, Site site) throws PatriusException {
		final KeplerianPropagator propagator = createDefaultPropagator();
		final PVCoordinates satPv = propagator.getPVCoordinates(date, getEme2000());
		final TopocentricFrame siteFrame = new TopocentricFrame(getEarth(), site.getPoint(), site.getName());
		final PVCoordinates sitePv = siteFrame.getPVCoordinates(date, getEme2000());
		final Vector3D siteSatVectorEme2000 = sitePv.getPosition().subtract(satPv.getPosition()).normalize();
		final Vector3D siteNormalVectorEarthFrame = siteFrame.getZenith();
		final Transform earth2Eme2000 = siteFrame.getParentShape().getBodyFrame().getTransformTo(getEme2000(), date);
		final Vector3D siteNormalVectorEme2000 = earth2Eme2000.transformPosition(siteNormalVectorEarthFrame);
		final double incidenceAngle = Vector3D.angle(siteNormalVectorEme2000, siteSatVectorEme2000);
		return Math.abs(Math.toDegrees(incidenceAngle));
	}

	/**
	 * Compute the best time for observation in a given window (regarding incidence)
	 * 
	 * @param accessWindow The access window to consider
	 * @throws PatriusException If a {@link PatriusException} occurs
	 * @return The best time for observation in the given window
	 */

	public AbsoluteDate computeBestObservationTime(Phenomenon accessWindow, Site site) throws PatriusException {
		final AbsoluteDateInterval accessInterval = accessWindow.getTimespan();
		AbsoluteDate date1 = accessInterval.getLowerData();
		AbsoluteDate date2 = accessInterval.getUpperData();
		double total_time = date2.durationFrom(date1);
		int time_step = 5;
		int n_iter = (int) total_time / time_step;
		AbsoluteDate best_date = date1;
		double best_incidence = getIncidence(date1, site);
		for (int i = 1; i < n_iter - 1; i++) {
			AbsoluteDate current_date = date1.shiftedBy(i * time_step);
			double current_incidence = getIncidence(current_date, site);
			if (current_incidence > best_incidence) {
				best_incidence = current_incidence;
				best_date = current_date;
			}
		}
		return best_date;
	}

	public boolean isCompatible(AbsoluteDateInterval dateInterval) {
		boolean compatible = true;
		if (this.observationPlan.isEmpty()) {
			compatible = true;
		} else {
			// If the observation plan is not empty, we need to check if the new observation
			// is compatible with the existing plan
			for (final Entry<Site, AttitudeLawLeg> obs : this.observationPlan.entrySet()) {
				// Getting the observation interval of the existing observation
				final AbsoluteDateInterval existingObsInterval = obs.getValue().getTimeInterval();
				// Checking if the new observation is compatible with the existing one
				if (dateInterval.getIntersectionWith(existingObsInterval) != null) {
					compatible = false;
					break;
				}
			}
		}
		return compatible;
	}

	
	/**
	 * Compute the observation plan.
	 * 
	 * @return the sites observation plan with one {@link AttitudeLawLeg} per
	 *         {@link Site}
	 * @throws PatriusException If a {@link PatriusException} occurs during the
	 *                          computations
	 */
	public Map<Site, AttitudeLawLeg> computeObservationPlan() throws PatriusException {
		
		logger.info("============= Computing Observation Plan =============");
		List<Entry<Site, Timeline>> entryList = new ArrayList<>(this.accessPlan.entrySet());
        entryList.sort(Comparator.comparing(entry -> entry.getKey().getScore(), Comparator.reverseOrder()));

		for (final Entry<Site, Timeline> entry : entryList) {
			// Scrolling through the entries of the accessPlan
			// Getting the target Site	
			final Site target = entry.getKey();
			logger.info("Current target site : " + target.getName());
			// Getting its access Timeline
			final Timeline timeline = entry.getValue();
			// Getting the access intervals
			final AbsoluteDateIntervalsList accessIntervals = new AbsoluteDateIntervalsList();
			double best_incidence = 0;
			AttitudeLawLeg best_LawLeg = new AttitudeLawLeg(null, null);
			for (final Phenomenon accessWindow : timeline.getPhenomenaList()) { 
				// The Phenomena are sorted chronologically so the accessIntervals List is too // access interval -> juste le temps
				final AbsoluteDateInterval accessInterval = accessWindow.getTimespan();
				accessIntervals.add(accessInterval);
				logger.info(accessInterval.toString());

				// Use this method to create your observation leg, see more help inside the
				// method.
				final AttitudeLaw observationLaw = createObservationLaw(target);
				
				final AbsoluteDate bestDate = computeBestObservationTime(accessWindow, target);				
				final AbsoluteDate obsStart = bestDate.shiftedBy(-ConstantsBE.INTEGRATION_TIME / 2);
				final AbsoluteDate obsEnd = bestDate.shiftedBy(ConstantsBE.INTEGRATION_TIME / 2);
				final AbsoluteDateInterval obsInterval = new AbsoluteDateInterval(obsStart, obsEnd);
				final AbsoluteDateInterval obsIntervalSlew = new AbsoluteDateInterval(obsStart.shiftedBy(-this.getSatellite().getMaxSlewDuration()),
						obsEnd.shiftedBy(this.getSatellite().getMaxSlewDuration())); // maximum interval needed in the worst case (maximum slew)

				// Boolean to check if the observation is compatible with our existing plan
				boolean obsCompatible = isCompatible(obsIntervalSlew);
				
				// If the observation is compatible with the existing plan, we can add it
				if (obsCompatible) {
					double incidence = getIncidence(bestDate, target);
					if (incidence > best_incidence) {
						best_incidence = incidence;
						final String legName = "OBS_" + target.getName();
						final AttitudeLawLeg obsLeg = new AttitudeLawLeg(observationLaw, obsInterval, legName);
						best_LawLeg = obsLeg;
					}
				}
			}
			if (best_incidence > 0) {
				this.observationPlan.put(target, best_LawLeg);
			}
		}

		return this.observationPlan;
	}

	/**
	 * Computes the cinematic plan.
	 * 
	 * @return a {@link StrictAttitudeLegsSequence} that gives all the cinematic
	 *         plan of the {@link Satellite}. It is a chronological sequence of all
	 *         the {@link AttitudeLawLeg} that are necessary to define the
	 *         {@link Attitude} of the {@link Satellite} during all the mission
	 *         horizon. Those legs can have 3 natures : pointing a target site,
	 *         pointing nadir and performing a slew between one of the two previous
	 *         kind of legs.
	 * @throws PatriusException
	 */
	public StrictAttitudeLegsSequence<AttitudeLeg> computeCinematicPlan() throws PatriusException {

		logger.info("============= Computing Cinematic Plan =============");

		// We first need to sort the observation plan by date
		List<Entry<Site, AttitudeLawLeg>> entryList = new ArrayList<>(observationPlan.entrySet());
		
		// Sort the list based on the date from obsLeg.getDate()
        entryList.sort(Comparator.comparing(entry -> entry.getValue().getDate()));

		Iterator<Entry<Site, AttitudeLawLeg>> iterator = entryList.iterator();

        if (iterator.hasNext()) {
            Entry<Site, AttitudeLawLeg> firstEntry = iterator.next();
            Site firstSite = firstEntry.getKey();
            AttitudeLawLeg firstObsLeg = firstEntry.getValue();

            // Add nadir1 and slew1 for the first observation
            final AttitudeLaw nadirLaw = this.getSatellite().getDefaultAttitudeLaw();
            final AbsoluteDate start = this.getStartDate();
            final AbsoluteDate endNadirLaw1 = firstObsLeg.getDate().shiftedBy(-getSatellite().getMaxSlewDuration());
            final AttitudeLawLeg nadir1 = new AttitudeLawLeg(nadirLaw, start, endNadirLaw1, "Nadir_Law_1" );
            final ConstantSpinSlew slew1 = new ConstantSpinSlew(nadirLaw.getAttitude(createDefaultPropagator(), endNadirLaw1, getEme2000()), firstObsLeg.getAttitude(createDefaultPropagator(), firstObsLeg.getDate(), getEme2000()), "Slew_Nadir_to_" + firstSite.getName());

            this.cinematicPlan.add(nadir1);
            this.cinematicPlan.add(slew1);
            this.cinematicPlan.add(firstObsLeg);

            // Handle the slews between consecutive observations
            Entry<Site, AttitudeLawLeg> prevEntry = firstEntry;
            while (iterator.hasNext()) {

                Entry<Site, AttitudeLawLeg> currentEntry = iterator.next();
                Site currentSite = currentEntry.getKey();
                Site previousSite = prevEntry.getKey();
                AttitudeLawLeg currentObsLeg = currentEntry.getValue();
                AttitudeLawLeg previousObsLeg = prevEntry.getValue();

        	    final KeplerianPropagator propagator = this.createDefaultPropagator();
    		    final AbsoluteDate dateEndPrevObs = previousObsLeg.getEnd();
    		    final AbsoluteDate dateStartCurObs = currentObsLeg.getDate();

				// One max slew duration between two observations is enough to add a nadir between them
				// In worst case scenario, we need 1/2 maw slew duration from one observation to nadir
				// and 1/2 max slew duration from nadir to the next observation so 1 max slew duration total
				float weightMaxSlewDuration = 1.2f;
				if (dateStartCurObs.durationFrom(dateEndPrevObs) > weightMaxSlewDuration * getSatellite().getMaxSlewDuration()) { 

					// Getting all dates needed to compute our slews
					final AbsoluteDate dateStartNadirLaw = dateEndPrevObs.shiftedBy(+0.5*weightMaxSlewDuration*getSatellite().getMaxSlewDuration());
					final AbsoluteDate dateEndNadirLaw = dateStartCurObs.shiftedBy(-0.5*weightMaxSlewDuration*getSatellite().getMaxSlewDuration());

					// Creating Attitudes for the slews 
					final Attitude startSlewObsNadirAttitude = previousObsLeg.getAttitude(propagator, dateEndPrevObs, getEme2000());
					final Attitude endSlewObsNadirAttitude = nadirLaw.getAttitude(propagator, dateStartNadirLaw, getEme2000());
					final Attitude startSlewNadirObsAttitude = nadirLaw.getAttitude(propagator, dateEndNadirLaw, getEme2000());
					final Attitude endSlewNadirObsAttitude = currentObsLeg.getAttitude(propagator, dateStartCurObs, getEme2000());
					
					// Compute slew from previous observation to nadir and nadir to next observation
					final ConstantSpinSlew slewPrevObsToNadir = new ConstantSpinSlew(startSlewObsNadirAttitude, endSlewObsNadirAttitude, "Slew_" + previousSite.getName() + "_to_Nadir");
					final ConstantSpinSlew slewNadirToCurObs = new ConstantSpinSlew(startSlewNadirObsAttitude, endSlewNadirObsAttitude, "Slew_Nadir_to_" + currentSite.getName());

					// Compute AttitudeLawLeg for Nadir
					final AttitudeLawLeg nadir = new AttitudeLawLeg(nadirLaw, dateStartNadirLaw, dateEndNadirLaw, "Nadir_Law");

					// Add all the elements to the cinematic plan
					this.cinematicPlan.add(slewPrevObsToNadir);
					this.cinematicPlan.add(nadir);
					this.cinematicPlan.add(slewNadirToCurObs);
					this.cinematicPlan.add(currentObsLeg);
				} else {
					// Case where the duration between two observations is less than the max slew duration
					// We directly go to 2nd observation without adding a nadir step
					// dateEndPrevObs dateStartCurObs
					final Attitude startObsAttitude = previousObsLeg.getAttitude(propagator, dateEndPrevObs, getEme2000());
					final Attitude endObsAttitude = currentObsLeg.getAttitude(propagator, dateStartCurObs, getEme2000());
					
					final ConstantSpinSlew currentSlew = new ConstantSpinSlew(startObsAttitude,endObsAttitude,"Slew_" + previousSite.getName() + "_to_" + currentSite.getName());
	
					this.cinematicPlan.add(currentSlew);
					this.cinematicPlan.add(currentObsLeg);

				}
                prevEntry = currentEntry;
            }

            // Add nadir2 and slew2 for the last observation
            final AbsoluteDate end = this.getEndDate();
            final AbsoluteDate startNadirLaw2 = prevEntry.getValue().getEnd().shiftedBy(getSatellite().getMaxSlewDuration());
            final AttitudeLawLeg nadir2 = new AttitudeLawLeg(nadirLaw, startNadirLaw2, end, "Nadir_Law_2");
            final ConstantSpinSlew slew2 = new ConstantSpinSlew(prevEntry.getValue().getAttitude(createDefaultPropagator(), prevEntry.getValue().getEnd(), getEme2000()), nadirLaw.getAttitude(createDefaultPropagator(), startNadirLaw2, getEme2000()), "Slew_" + prevEntry.getKey().getName() + "_to_Nadir");

            this.cinematicPlan.add(slew2);
            this.cinematicPlan.add(nadir2);
		}


		/**
		 * Now your job is finished, the two following methods will finish the job for
		 * you : checkCinematicPlan() will check that each slew's duration is longer
		 * than the theoritical duration it takes to perform the same slew. Then, if the
		 * cinematic plan is valid, computeFinalScore() will compute the score of your
		 * observation plan. Finaly, generateVTSVisualization will write all the
		 * ephemeris (Position/Velocity + Attitude) and generate a VTS simulation that
		 * you will be able to play to visualize and validate your plans.
		 */
		return this.cinematicPlan;
	}

	/**
	 * [COMPLETE THIS METHOD TO ACHIEVE YOUR PROJECT]
	 * 
	 * Create an observation leg, that is to say an {@link AttitudeLaw} that give
	 * the {@link Attitude} (pointing direction) of the {@link Satellite} in order
	 * to perform the observation of the input target {@link Site}.
	 * 
	 * An {@link AttitudeLaw} is an {@link AttitudeProvider} providing the method
	 * {@link AttitudeProvider#getAttitude()} which can be used to compute the
	 * {@link Attitude} of the {@link Satellite} at any given {@link AbsoluteDate}
	 * (instant) during the mission horizon.
	 * 
	 * An {@link AttitudeLaw} is valid at anu time in theory.
	 * 
	 * @param target Input target {@link Site}
	 * @return An {@link AttitudeLawLeg} adapted to the observation.
	 */
	private AttitudeLaw createObservationLaw(Site target) {
		/**
		 * To perform an observation, the satellite needs to point the target for a
		 * fixed duration.
		 * 
		 * Here, you will use the {@link TargetGroundPointing}. This law provides a the
		 * Attitude of a Satellite that only points one target at the surface of a
		 * BodyShape. The earth object from the SimpleMission is a BodyShape and we
		 * remind you that the Site object has an attribute which is a GeodeticPoint.
		 * Use those informations to your advantage to build a TargetGroundPointing.
		 * 
		 * Note : to avoid unusual behavior of the TargetGroundPointing law, we advise
		 * you use the following constructor : TargetGroundPointing(BodyShape, Vector3D,
		 * Vector3D, Vector3D) specifying the line of sight axis and the normal axis.
		 */
		
		TargetGroundPointing satAttitude = new TargetGroundPointing(this.getEarth(), target.getPoint(), this.getSatellite().getSensorAxis(), this.getSatellite().getFrameXAxis()); 
		return satAttitude;
	}

	/**
	 * @return the accessPlan
	 */
	public Map<Site, Timeline> getAccessPlan() {
		return this.accessPlan;
	}

	/**
	 * @return the observationPlan
	 */
	public Map<Site, AttitudeLawLeg> getObservationPlan() {
		return this.observationPlan;
	}

	/**
	 * @return the cinematicPlan
	 */
	public StrictAttitudeLegsSequence<AttitudeLeg> getCinematicPlan() {
		return this.cinematicPlan;
	}

	@Override
	public String toString() {
		return "CompleteMission [name=" + this.getName() + ", startDate=" + this.getStartDate() + ", endDate="
				+ this.getEndDate() + ", satellite=" + this.getSatellite() + "]";
	}
}
